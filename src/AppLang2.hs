{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
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
import Prelude hiding (seq, (<>))

-- Lang

data Lang :: * -> * -> * where
  Return :: a -> Lang c a
  Lit :: c -> Lang c ()
  Sum :: [Lang c a] -> Lang c a
  (:.:) :: Lang c a -> Lang c b -> Lang c (a, b)
  Map :: (a -> b) -> Lang c a -> Lang c b
  Bind :: Lang c a -> (a -> Lang c b) -> Lang c b

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

(<>) :: Lang c a -> Lang c b -> Lang c (a, b)
(<>) Void _ = Void
(<>) _ Void = Void
(<>) (Return a) x = (a,) <$> x
(<>) x (Return a) = (,a) <$> x
(<>) (Map f x) (Map g y) = (f *** g) <$> x <> y
(<>) (Map f x) y = first f <$> x <> y
(<>) x (Map f y) = second f <$> x <> y
(<>) x y = x :.: y

instance Functor (Lang c) where
  fmap _ Void = Void
  fmap f (Return a) = Return (f a)
  fmap f (Map g x) = fmap (f . g) x
  fmap f x = Map f x

instance Applicative (Lang c) where
  pure = Return
  x <*> y = uncurry ($) <$> (x <> y)

instance Alternative (Lang c) where
  empty = Sum []
  Void <|> y = y
  x <|> Void = x
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
nu (x :.: y) = (,) <$> nu x <*> nu y
nu (Map f x) = fmap f (nu x)
nu (Bind x f) = nu x >>= nu . f

delta :: Eq c => Lang c a -> c -> Lang c a
delta Void = const Void
delta (Return _) = const Void
delta (Lit c) = \c' -> if c == c' then pure () else Void
delta (Sum xs) = \c -> asum $ map (`delta` c) xs
delta (x :.: y) = \c -> asum $ (delta x c <> y) : [(a,) <$> delta y c | a <- nu x]
delta (Map f x) = (f <$>) . delta x
delta (Bind x f) = \c -> asum $ (delta x c >>= f) : [delta (f a) c | a <- nu x]

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
  x >>= f = Gen $ do
    unGen x >>= \case
      Just a -> unGen (f a)
      Nothing -> pure Nothing

sample :: Lang c a -> Gen a
sample (Lit _) = pure ()
sample Void = gfail
sample (Return a) = pure a
sample (Sum []) = gfail
sample (Sum xs) = oneof (sample <$> xs)
sample (x :.: y) = (,) <$> sample x <*> sample y
sample (Map f x) = f <$> sample x
sample (Bind x f) = sample x >>= sample . f

mcts :: Ord a => Int -> (a -> Bool) -> Lang c a -> IO (Set a)
mcts n p =
  fmap (Set.fromList . filter p . catMaybes)
    . replicateM n
    . generate
    . sample

choiceFitness ::
  (Eq c, Ord c, Ord a) =>
  [c] ->
  Int ->
  (a -> Bool) ->
  Lang c a ->
  IO [(c, Double)]
choiceFitness alpha n p l =
  zip alpha . normalize
    <$> mapM ((Set.size <$>) . mcts n p . delta l) alpha
  where
    normalize cs =
      let s = fromIntegral (sum cs)
       in (/ s) . fromIntegral <$> cs

---------------------------------------
-- Examples
---------------------------------------

newtype Choice = Choice (String, String)
  deriving (Eq, Ord)

instance Show Choice where
  show (Choice (t, l)) = t ++ "_" ++ l

select :: String -> [(String, Lang Choice a)] -> Lang Choice a
select s = asum . map (\(i, l) -> Lit (Choice (s, i)) *> l)

genPair :: Lang Choice (Int, Int)
genPair =
  (,) <$> select "first" [(show n, pure n) | n <- [0, 1, 2]]
    <*> select "second" [(show n, pure n) | n <- [0, 1, 2]]

pairAlpha :: [Choice]
pairAlpha =
  [Choice ("first", show n) | n <- [0 :: Int, 1, 2]]
    ++ [Choice ("second", show n) | n <- [0 :: Int, 1, 2]]

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
genTree = aux (4 :: Int)
  where
    aux 0 = pure Leaf
    aux n =
      select
        "Tree"
        [ ("leaf", pure Leaf),
          ( "node",
            do
              x <- genInt
              l <- aux (n - 1)
              r <- aux (n - 1)
              pure (Node l x r)
          )
        ]
    genInt = select "Num" [(show n, pure n) | n <- [0 .. 9]]

genBST :: Lang Choice Tree
genBST = aux 0 9
  where
    aux mn mx | mn > mx = pure Leaf
    aux mn mx =
      select
        "Tree"
        [ ("leaf", pure Leaf),
          ( "node",
            do
              x <- genInt mn mx
              l <- aux mn (x - 1)
              r <- aux (x + 1) mx
              pure (Node l x r)
          )
        ]
    genInt mn mx = select "Num" [(show n, pure n) | n <- [mn .. mx]]

treeAlpha :: [Choice]
treeAlpha =
  [Choice ("Tree", "leaf"), Choice ("Tree", "node")]
    ++ [Choice ("Num", show n) | n <- [0 :: Int .. 9]]
