{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}

module Lang where

import Control.Applicative (Alternative (..))
import Control.Monad (MonadPlus, ap, foldM, msum)
import Data.List (genericLength)
import Data.Maybe (catMaybes)
import Data.Set (Set)
import qualified Data.Set as Set

data Lang c a where
  Void :: Lang c a
  Return :: a -> Lang c a
  Lit :: c -> Lang c ()
  (:+:) :: Lang c a -> Lang c a -> Lang c a
  (:>>=) :: Lang c a -> (a -> Lang c b) -> Lang c b

instance Functor (Lang c) where
  fmap f Void = Void
  fmap f (Return x) = Return (f x)
  fmap f (Lit c) = Lit c >> Return (f ())
  fmap f (l1 :+: l2) = fmap f l1 <|> fmap f l2
  fmap f (x :>>= mf) = x >>= fmap f . mf

instance Applicative (Lang c) where
  pure = return
  (<*>) = ap

instance Monad (Lang c) where
  return = Return
  Void >>= f = Void
  Return x >>= f = f x
  l >>= f = l :>>= f

instance Alternative (Lang c) where
  empty = Void
  Void <|> l = l
  l <|> Void = l
  l1 <|> l2 = l1 :+: l2

instance MonadPlus (Lang c)

nu :: Lang c a -> [a]
nu Void = []
nu (Return x) = [x]
nu (Lit _) = []
nu (t1 :+: t2) = nu t1 ++ nu t2
nu (t :>>= f) = nu t >>= nu . f

delta :: Eq c => Lang c a -> c -> Lang c a
delta Void = const Void
delta (Return _) = const Void
delta (Lit c) = \c' -> if c == c' then pure () else Void
delta (l1 :+: l2) = \c -> delta l1 c <|> delta l2 c
delta (l :>>= f) = \c -> (delta l c >>= f) <|> msum [delta (f x) c | x <- nu l]

type Choice = (String, String)

select :: String -> [(String, Lang Choice a)] -> Lang Choice a
select s = msum . map (\(i, l) -> Lit (s, i) >> l)

data Tree = Node Tree Int Tree | Leaf
  deriving (Eq, Ord, Show)

genTree :: Int -> Int -> Lang Choice Tree
genTree min max | min > max = pure Leaf
genTree min max =
  select
    "Tree"
    [ ("leaf", pure Leaf),
      ( "node",
        do
          x <- select "Num" [(show n, pure n) | n <- [min .. max]]
          l <- genTree min (x - 1)
          r <- genTree (x + 1) max
          pure (Node l x r)
      )
    ]

treeAlpha :: Int -> Int -> [Choice]
treeAlpha min max = [("Tree", "leaf"), ("Tree", "node")] ++ [("Num", show n) | n <- [min .. max]]

genPair :: Lang Choice (Int, Int)
genPair = do
  i <- select "first" [(show n, pure n) | n <- [0, 1, 2]]
  j <- select "second" [(show n, pure n) | n <- [0, 1, 2]]
  pure (i, j)

pairAlpha :: [Choice]
pairAlpha = [("first", show n) | n <- [0, 1, 2]] ++ [("second", show n) | n <- [0, 1, 2]]

contains :: (Eq a, Eq c) => Lang c a -> [c] -> [a]
contains t = nu . foldl delta t

finMeasure :: Eq c => [c] -> Lang c a -> Integer
finMeasure _ Void = 0
finMeasure alpha l = genericLength (nu l) + sum [finMeasure alpha (delta l c) | c <- alpha]

finEnumerate :: (Eq c, Ord a) => [c] -> Lang c a -> Set a
finEnumerate _ Void = Set.empty
finEnumerate alpha l = Set.fromList (nu l) `Set.union` Set.unions [finEnumerate alpha (delta l c) | c <- alpha]
