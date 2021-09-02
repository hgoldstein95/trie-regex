{-# LANGUAGE GADTs #-}

module Regex where

import Test.QuickCheck (Arbitrary (..), oneof, resize, sized)
import Trie (Trie)
import qualified Trie
import Prelude hiding ((+), (<>))

data Regex a where
  Void :: Regex a
  Lit :: a -> Regex a
  (:+:) :: Regex a -> Regex a -> Regex a
  (:<>:) :: Regex a -> Regex a -> Regex a
  Star :: Regex a -> Regex a
  deriving (Eq)

instance Show a => Show (Regex a) where
  show Void = "∅"
  show (Lit x) = show x
  show (r1 :+: r2) = "(" ++ show r1 ++ " + " ++ show r2 ++ ")"
  show (r1 :<>: r2) = "(" ++ show r1 ++ show r2 ++ ")"
  show (Star r) = show r ++ "*"

void :: Regex a
void = Void

star :: Regex a -> Regex a
star = Star

(+) :: Eq a => Regex a -> Regex a -> Regex a
r1 + r2 = r1 :+: r2

(<>) :: Eq a => Regex a -> Regex a -> Regex a
r1 <> r2 = r1 :<>: r2

empty :: Regex a
empty = Star Void

lit :: a -> Regex a
lit = Lit

nu :: Regex a -> Bool
nu Void = False
nu (Lit _) = False
nu (t1 :+: t2) = nu t1 || nu t2
nu (t1 :<>: t2) = nu t1 && nu t2
nu (Star _) = True

delta :: Eq a => Regex a -> a -> Regex a
delta Void = const void
delta (Lit c) = \c' -> if c == c' then empty else void
delta (t1 :+: t2) = \c -> delta t1 c + delta t2 c
delta (t1 :<>: t2) = \c -> if nu t1 then delta t1 c + delta t2 c else delta t1 c
delta (Star t) = \c -> delta t c <> star t

contains :: Eq a => Regex a -> [a] -> Bool
contains t = nu . foldl delta t

instance (Eq a, Arbitrary a) => Arbitrary (Regex a) where
  arbitrary = resize 10 $ sized aux
    where
      aux 0 =
        oneof
          [ pure void,
            lit <$> arbitrary
          ]
      aux n =
        oneof
          [ pure void,
            lit <$> arbitrary,
            (+) <$> aux (n `div` 2) <*> aux (n `div` 2),
            (<>) <$> aux (n `div` 2) <*> aux (n `div` 2),
            star <$> aux (n - 1)
          ]

  shrink Void = []
  shrink (Lit _) = []
  shrink (r1 :+: r2) = [r1, r2]
  shrink (r1 :<>: r2) = [r1, r2]
  shrink (Star r) = [r]

toTrie :: Eq a => Regex a -> Trie a
toTrie Void = Trie.void
toTrie (Lit x) = Trie.lit x
toTrie (r1 :+: r2) = toTrie r1 Trie.+ toTrie r2
toTrie (r1 :<>: r2) = toTrie r1 Trie.<> toTrie r2
toTrie (Star r) = Trie.star (toTrie r)
