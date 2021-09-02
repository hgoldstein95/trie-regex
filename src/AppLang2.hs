{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE UndecidableInstances #-}

module AppLang where

import Control.Applicative (Alternative (..))
import Control.Arrow (Arrow (first, second), (***))
import Control.Monad (ap, replicateM)
import Data.Foldable (asum)
import Data.List (genericLength, intercalate)
import Data.Maybe (catMaybes, isJust)
import Data.Set (Set)
import qualified Data.Set as Set
import Test.QuickCheck (Gen, elements, oneof)
import qualified Test.QuickCheck as QC
import Prelude hiding (seq, (<>))

-- Lang

data Lang :: * -> * -> * where
  Return :: a -> Lang c a
  Lit :: c -> Lang c ()
  Sum :: [Lang c a] -> Lang c a
  (:*:) :: Lang c a -> Lang c b -> Lang c (a, b)
  Map :: (a -> b) -> Lang c a -> Lang c b

-- Void as a synonym for Sum []

void :: Lang c a
void = Sum []

pattern Void = Sum []

-- Show

instance Show c => Show (Lang c a) where
  show (Return _) = "ε"
  show (Lit c) = show c
  show Void = "∅"
  show (Sum ls) = "(" ++ intercalate " + " (map show ls) ++ ")"
  show ((:*:) l1 l2) = show l1 ++ " " ++ show l2
  show (Map _ l) = show l

-- Smart constructors / instances

(<>) :: Lang c a -> Lang c b -> Lang c (a, b)
(<>) Void _ = Void
(<>) _ Void = Void
(<>) (Return x) l = (x,) <$> l
(<>) l (Return x) = (,x) <$> l
(<>) (Map f l1) (Map g l2) = (f *** g) <$> l1 <> l2
(<>) (Map f l1) l2 = first f <$> l1 <> l2
(<>) l1 (Map f l2) = second f <$> l1 <> l2
(<>) l1 l2 = l1 :*: l2

instance Functor (Lang c) where
  fmap _ Void = Void
  fmap f (Return x) = Return (f x)
  fmap f (Map g l) = fmap (f . g) l
  fmap f l = Map f l

instance Applicative (Lang c) where
  pure = Return
  l1 <*> l2 = uncurry ($) <$> (l1 <> l2)

instance Alternative (Lang c) where
  empty = Sum []
  Void <|> y = y
  x <|> Void = x
  Sum xs <|> Sum ys = Sum (xs ++ ys)
  Sum xs <|> y = Sum (xs ++ [y])
  x <|> Sum ys = Sum (x : ys)
  x <|> y = Sum [x, y]

-- Nullability and Derivatives

nu :: Lang c a -> [a] -- This is an Alternative homomorphism into list!
nu (Lit _) = empty
nu Void = empty
nu (Return x) = pure x
nu (Sum ls) = foldl1 (<|>) (map nu ls)
nu (l1 :*: l2) = (,) <$> nu l1 <*> nu l2
nu (Map f l) = fmap f (nu l)

delta :: Eq c => Lang c a -> c -> Lang c a
delta Void = const Void
delta (Return _) = const Void
delta (Lit c) = \c' -> if c == c' then pure () else Void
delta (Sum ls) = \c -> asum $ map (`delta` c) ls
delta (l1 :*: l2) = \c ->
  asum $
    (delta l1 c <> l2) :
      [(x,) <$> delta l2 c | x <- nu l1]
delta (Map f l) = (f <$>) . delta l

-- Folds with delta

contains :: (Eq a, Eq c) => Lang c a -> [c] -> [a]
contains t = nu . foldl delta t

measure :: Eq c => [c] -> Lang c a -> Integer
measure _ Void = 0
measure alpha l =
  genericLength (nu l)
    + sum [measure alpha (delta l c) | c <- alpha]

enumerate :: (Eq c, Ord a) => [c] -> Lang c a -> Set a
enumerate _ Void = Set.empty
enumerate alpha l =
  Set.fromList (nu l)
    `Set.union` Set.unions [enumerate alpha (delta l c) | c <- alpha]

-- Gen and MCTS

newtype Gen' a = Gen' {unGen' :: Gen (Maybe a)}
  deriving (Functor)

generate :: Gen' a -> IO (Maybe a)
generate = QC.generate . unGen'

instance Applicative Gen' where
  pure = return
  (<*>) = ap

instance Monad Gen' where
  return = Gen' . pure . Just
  (Gen' x) >>= f = Gen' $ do
    x >>= \case
      Just a -> unGen' (f a)
      Nothing -> pure Nothing

sample :: Lang c a -> Gen' a
sample (Lit c) = pure ()
sample Void = Gen' (pure Nothing)
sample (Return a) = pure a
sample (Sum []) = Gen' (pure Nothing)
sample (Sum xs) = Gen' . oneof . (unGen' . sample <$>) $ xs
sample (x :*: y) = (,) <$> sample x <*> sample y
sample (Map f x) = f <$> sample x

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
  normalize
    <$> mapM
      (\c -> fmap ((c,) . Set.size) . mcts n p . delta l $ c)
      alpha
  where
    normalize cs =
      let s = fromIntegral $ sum (snd <$> cs)
       in second ((/ s) . fromIntegral) <$> cs

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
  [Choice ("first", show n) | n <- [0, 1, 2]]
    ++ [Choice ("second", show n) | n <- [0, 1, 2]]

data Tree = Node Tree Int Tree | Leaf
  deriving (Eq, Ord, Show)

toList :: Tree -> [Int]
toList Leaf = []
toList (Node l x r) = toList l ++ [x] ++ toList r

isBST :: Tree -> Bool
isBST (Node l x r) =
  isBST l
    && isBST r
    && all (< x) (toList l)
    && all (> x) (toList r)
isBST Leaf = True

genTree :: Lang Choice Tree
genTree = aux 4
  where
    aux 0 = pure Leaf
    aux n =
      select
        "Tree"
        [ ("leaf", pure Leaf),
          ("node", node <$> genInt <*> aux (n - 1) <*> aux (n - 1))
        ]
    genInt = select "Num" [(show n, pure n) | n <- [0 .. 9]]
    node x l r = Node l x r

treeAlpha :: [Choice]
treeAlpha =
  [Choice ("Tree", "leaf"), Choice ("Tree", "node")]
    ++ [Choice ("Num", show n) | n <- [0 .. 9]]
