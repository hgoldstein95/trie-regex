{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}

module AppLang where

import Control.Applicative (Alternative (..))
import Control.Monad (MonadPlus, ap, foldM, msum)
import Data.Foldable (asum)
import Data.List (genericLength)
import Data.Maybe (catMaybes)
import Data.Set (Set)
import qualified Data.Set as Set
import Prelude hiding (seq)

data Lang c a where
  Void :: Lang c a
  Return :: a -> Lang c a
  Lit :: c -> Lang c ()
  (:+:) :: Lang c a -> Lang c a -> Lang c a
  (:*:) :: Lang c (a -> b) -> Lang c a -> Lang c b

instance Functor (Lang c) where
  fmap f Void = Void
  fmap f (Return x) = Return (f x)
  fmap f (Lit c) = Lit c *> Return (f ())
  fmap f (l1 :+: l2) = fmap f l1 <|> fmap f l2
  fmap f (g :*: l) = fmap (f .) g <*> l

instance Applicative (Lang c) where
  pure = Return
  Void <*> _ = Void
  _ <*> Void = Void
  Return f <*> l = f <$> l
  l <*> Return x = ($ x) <$> l
  l1 <*> l2 = l1 :*: l2

instance Alternative (Lang c) where
  empty = Void
  Void <|> l = l
  l <|> Void = l
  l1 <|> l2 = l1 :+: l2

nu :: Lang c a -> [a] -- This is an Alternative homomorphism into list!
nu (Lit _) = empty
nu Void = empty
nu (Return x) = pure x
nu (l1 :+: l2) = nu l1 <|> nu l2
nu (f :*: l) = nu f <*> nu l

delta :: Eq c => Lang c a -> c -> Lang c a
delta Void = const Void
delta (Return _) = const Void
delta (Lit c) = \c' -> if c == c' then pure () else Void
delta (l1 :+: l2) = \c -> delta l1 c <|> delta l2 c
delta (f :*: l) = \c -> (delta f c <*> l) <|> asum [g <$> delta l c | g <- nu f]

type Choice = (String, String)

select :: String -> [(String, Lang Choice a)] -> Lang Choice a
select s = asum . map (\(i, l) -> Lit (s, i) *> l)

data Tree = Node Tree Int Tree | Leaf
  deriving (Eq, Ord, Show)

genTree :: Lang Choice Tree
genTree = aux 4
  where
    aux 0 = pure Leaf
    aux n =
      select
        "Tree"
        [ ("leaf", pure Leaf),
          ( "node",
            Node <$> aux (n - 1)
              <*> select "Num" [(show n, pure n) | n <- [0, 1, 2]]
              <*> aux (n - 1)
          )
        ]

treeAlpha :: [Choice]
treeAlpha =
  [("Tree", "leaf"), ("Tree", "node")]
    ++ [("Num", show n) | n <- [0, 1, 2]]

genPair :: Lang Choice (Int, Int)
genPair =
  (,) <$> select "first" [(show n, pure n) | n <- [0, 1, 2]]
    <*> select "second" [(show n, pure n) | n <- [0, 1, 2]]

pairAlpha :: [Choice]
pairAlpha =
  [("first", show n) | n <- [0, 1, 2]]
    ++ [("second", show n) | n <- [0, 1, 2]]

contains :: (Eq a, Eq c) => Lang c a -> [c] -> [a]
contains t = nu . foldl delta t

finMeasure :: Eq c => [c] -> Lang c a -> Integer
finMeasure _ Void = 0
finMeasure alpha l =
  genericLength (nu l)
    + sum [finMeasure alpha (delta l c) | c <- alpha]

finEnumerate :: (Eq c, Ord a) => [c] -> Lang c a -> Set a
finEnumerate _ Void = Set.empty
finEnumerate alpha l =
  Set.fromList (nu l)
    `Set.union` Set.unions [finEnumerate alpha (delta l c) | c <- alpha]
