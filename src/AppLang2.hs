{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}

module AppLang where

import Control.Applicative (Alternative (..))
import Control.Arrow (Arrow (first, second), (***))
import Control.Monad (ap, replicateM)
import Data.Foldable (asum)
import Data.List (genericLength, intercalate)
import Data.Maybe (catMaybes)
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Test.QuickCheck as QC
import Text.Printf (printf)

class Joinable (f :: * -> *) where
  (><) :: f a -> f b -> f (a, b)

instance Joinable [] where
  (><) = zip

-- Lang

data Lang :: * -> * -> * where
  Lit :: c -> Lang c ()
  Sum :: [Lang c a] -> Lang c a
  (:.:) :: Lang c a -> Lang c b -> Lang c (a, b)
  Return :: a -> Lang c a
  Map :: (a -> b) -> Lang c a -> Lang c b
  Bind :: Lang c a -> (a -> Lang c b) -> Lang c b

-- TODO: Could add a boolean tag for isApplicative in the type
isApplicative :: Lang c a -> Bool
isApplicative (Lit _) = True
isApplicative (Sum xs) = all isApplicative xs
isApplicative (x :.: y) = isApplicative x && isApplicative y
isApplicative (Return _) = True
isApplicative (Map _ x) = isApplicative x
isApplicative (Bind _ _) = False

-- Void as a synonym for Sum []

pattern Void :: Lang c a
pattern Void = Sum []

-- Show

instance Show c => Show (Lang c a) where
  show (Return _) = "ε"
  show (Lit c) = show c
  show Void = "∅"
  show (Sum xs) = "(" ++ intercalate " + " (map show xs) ++ ")"
  show (x :.: y) = show x ++ " " ++ show y
  show (Map _ l) = show l
  show (Bind _ _) = "(... >>= ...)"

-- Smart constructors / instances

instance Joinable (Lang c) where
  Void >< _ = Void
  _ >< Void = Void
  Return a >< x = (a,) <$> x
  x >< Return a = (,a) <$> x
  Map f x >< Map g y = (f *** g) <$> x >< y
  Map f x >< y = first f <$> x >< y
  x >< Map f y = second f <$> x >< y
  x >< y = x :.: y

instance Functor (Lang c) where
  fmap _ Void = Void
  fmap f (Return a) = Return (f a)
  fmap f (Map g x) = fmap (f . g) x
  fmap f x = Map f x

instance Applicative (Lang c) where
  pure = Return
  x <*> y = uncurry ($) <$> (x >< y)

instance Alternative (Lang c) where
  empty = Sum []
  Sum xs <|> Sum ys = Sum (xs ++ ys)
  Sum xs <|> y = Sum (xs ++ [y])
  x <|> Sum ys = Sum (x : ys)
  x <|> y = Sum [x, y]

instance Monad (Lang c) where
  return = pure
  Void >>= _ = Void
  Return a >>= f = f a
  Map g a >>= f = a >>= f . g
  x >>= f = Bind x f

-- Nullability and Derivatives

nu :: Lang c a -> [a] -- This is an Alternative homomorphism into list!
nu (Lit _) = empty
nu Void = empty
nu (Return a) = pure a
nu (Sum xs) = foldl1 (<|>) (map nu xs)
nu (x :.: y) = nu x >< nu y
nu (Map f x) = fmap f (nu x)
nu (Bind x f) = nu x >>= nu . f

delta :: Eq c => Lang c a -> c -> Lang c a
delta Void = const Void
delta (Return _) = const Void
delta (Lit c) = \c' -> if c == c' then pure () else Void
delta (Sum xs) = \c -> asum $ map (`delta` c) xs
delta (Map f x) = (f <$>) . delta x
delta (x :.: y) =
  \c -> asum $ (delta x c >< y) : [delta ((a,) <$> y) c | a <- nu x]
delta (Bind x f) =
  \c -> asum $ (delta x c >>= f) : [delta (f a) c | a <- nu x]

-- Folds with delta

contains :: (Eq a, Eq c) => Lang c a -> [c] -> [a]
contains x = nu . foldl delta x

measure :: Eq c => [c] -> Lang c a -> Integer
measure _ Void = 0
measure alpha x =
  genericLength (nu x)
    + sum [measure alpha (delta x c) | c <- alpha]

enumerate :: (Eq c, Ord a) => [c] -> Lang c a -> Set a
enumerate _ Void = Set.empty
enumerate alpha x =
  Set.fromList (nu x)
    `Set.union` Set.unions [enumerate alpha (delta x c) | c <- alpha]

-- Gen and MCTS

newtype Gen a = Gen {unGen :: QC.Gen (Maybe a)}
  deriving (Functor)

oneof :: [Gen a] -> Gen a
oneof = Gen . QC.oneof . (unGen <$>)

gfail :: Gen a
gfail = Gen (pure Nothing)

generate :: Gen a -> IO (Maybe a)
generate = QC.generate . unGen

instance Applicative Gen where
  pure = return
  (<*>) = ap

instance Monad Gen where
  return = Gen . pure . Just
  x >>= f = Gen $ unGen x >>= maybe (pure Nothing) (unGen . f)

instance Joinable Gen where
  x >< y = (,) <$> x <*> y

sample :: Lang c a -> Gen a
sample (Lit _) = pure ()
sample Void = gfail
sample (Return a) = pure a
sample (Sum []) = gfail
sample (Sum xs) = oneof (sample <$> xs)
sample (x :.: y) = sample x >< sample y
sample (Map f x) = f <$> sample x
sample (Bind x f) = sample x >>= sample . f

mcts :: Ord a => Int -> (a -> Bool) -> Lang c a -> IO (Set a)
mcts n p =
  fmap (Set.fromList . filter p . catMaybes)
    . replicateM n
    . generate
    . sample

newtype ChoiceFitness c = ChoiceFitness [(c, Double)]

instance Show c => Show (ChoiceFitness c) where
  show (ChoiceFitness []) = ""
  show (ChoiceFitness ((c, d) : cs)) = show c ++ ":\t" ++ printf "%.4f" d ++ "\n" ++ show (ChoiceFitness cs)

choiceFitness ::
  (Eq c, Ord c, Ord a) =>
  [c] ->
  Int ->
  (a -> Bool) ->
  Lang c a ->
  IO (ChoiceFitness c, Set a)
choiceFitness alpha n p l = do
  s <- mapM (mcts n p . delta l) alpha
  let ds = zip alpha . normalize . map Set.size $ s
  pure (ChoiceFitness ds, Set.unions s)
  where
    normalize cs =
      let s = fromIntegral (sum cs)
       in if s == 0 then 1 <$ cs else (/ s) . fromIntegral <$> cs

-- Off the deep end?

goalTotal :: Int
goalTotal = 10000

naiveGen :: (Ord a, Ord c) => (a -> Bool) -> Lang c a -> IO (Set a)
naiveGen p g = aux Set.empty
  where
    aux acc | Set.size acc >= goalTotal = pure acc
    aux acc = do
      x <- generate $ sample g
      case x of
        Just a | p a -> aux (Set.insert a acc)
        _ -> aux acc

derivGen :: (Ord a, Ord c) => [c] -> (a -> Bool) -> Lang c a -> IO (Set a)
derivGen alpha p initG = aux Set.empty initG
  where
    aux acc _ | Set.size acc >= goalTotal = pure acc
    aux acc Void = aux acc initG
    aux acc g = do
      (f, s) <- choiceFitness alpha sampleSize p g
      c <- QC.generate $ pickChar f
      aux (Set.unions [acc, s, Set.fromList . filter p . nu $ g]) (delta g c)
    pickChar (ChoiceFitness cs) =
      QC.frequency [(round (d * fromIntegral sampleSize), pure c) | (c, d) <- cs]
    sampleSize = 100

---------------------------------------
-- Examples
---------------------------------------

newtype Choice = Choice String
  deriving (Eq, Ord)

instance Show Choice where
  show (Choice t) = t

select :: [(String, Lang Choice a)] -> Lang Choice a
select = asum . map (\(i, l) -> Lit (Choice i) *> l)

genPair :: Lang Choice (Int, Int)
genPair =
  (,) <$> select [("first_" ++ show n, pure n) | n <- [0, 1, 2]]
    <*> select [("second_" ++ show n, pure n) | n <- [0, 1, 2]]

pairAlpha :: [Choice]
pairAlpha =
  [Choice ("first_" ++ show n) | n <- [0 :: Int, 1, 2]]
    ++ [Choice ("second_" ++ show n) | n <- [0 :: Int, 1, 2]]

data Tree = Node Tree Int Tree | Leaf
  deriving (Eq, Ord, Show)

toList :: Tree -> [Int]
toList Leaf = []
toList (Node l x r) = toList l ++ [x] ++ toList r

isBST :: Tree -> Bool
isBST Leaf = True
isBST (Node l x r) =
  isBST l
    && isBST r
    && all (< x) (toList l)
    && all (> x) (toList r)

genTree :: Lang Choice Tree
genTree = aux (5 :: Int)
  where
    aux 0 = pure Leaf
    aux n =
      select
        [ ( "leaf",
            pure Leaf
          ),
          ( "node",
            do
              x <- genInt
              l <- aux (n - 1)
              r <- aux (n - 1)
              pure (Node l x r)
          )
        ]
    genInt = select [(show n, pure n) | n <- [0 .. 9]]

genBST :: Lang Choice Tree
genBST = aux 0 9
  where
    aux mn mx | mn > mx = pure Leaf
    aux mn mx =
      select
        [ ( "leaf",
            pure Leaf
          ),
          ( "node",
            do
              x <- genInt mn mx
              l <- aux mn (x - 1)
              r <- aux (x + 1) mx
              pure (Node l x r)
          )
        ]
    genInt mn mx = select [(show n, pure n) | n <- [mn .. mx]]

treeAlpha :: [Choice]
treeAlpha =
  [Choice "leaf", Choice "node"]
    ++ [Choice (show n) | n <- [0 :: Int .. 9]]
