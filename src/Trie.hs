module Trie where

import Test.QuickCheck (Arbitrary (..), oneof, sized)
import Prelude hiding ((+), (<>))

data Trie a = Trie
  { nu :: Bool,
    delta :: a -> Trie a
  }

empty :: Trie a
empty = star void

void :: Trie a
void =
  Trie
    { nu = False,
      delta = const void
    }

lit :: Eq a => a -> Trie a
lit c =
  Trie
    { nu = False,
      delta = \c' -> if c == c' then empty else void
    }

(+) :: Trie a -> Trie a -> Trie a
t1 + t2 =
  Trie
    { nu = nu t1 || nu t2,
      delta = \c -> delta t1 c + delta t2 c
    }

(<>) :: Trie a -> Trie a -> Trie a
t1 <> t2 =
  Trie
    { nu = nu t1 && nu t2,
      delta = \c -> delta t1 c + (if nu t1 then delta t2 c else void)
    }

star :: Trie a -> Trie a
star t =
  Trie
    { nu = True,
      delta = \c -> delta t c <> star t
    }

contains :: Trie a -> [a] -> Bool
contains t = nu . foldl delta t