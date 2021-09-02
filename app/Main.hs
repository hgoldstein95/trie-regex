module Main where

import Regex (Regex, toTrie)
import qualified Regex
import Test.QuickCheck
  ( Arbitrary (arbitrary),
    Property,
    elements,
    ioProperty,
    listOf,
    quickCheck,
    resize,
    verboseCheck,
    (===),
  )
import qualified Trie

newtype ReChar = ReChar {getChar :: Char}
  deriving (Eq)

instance Arbitrary ReChar where
  arbitrary = ReChar <$> elements ['a', 'b', 'c']

instance Show ReChar where
  show (ReChar c) = [c]

newtype ReString = ReString {getChars :: [ReChar]}
  deriving (Eq)

instance Arbitrary ReString where
  arbitrary = ReString <$> resize 10 (listOf arbitrary)

instance Show ReString where
  show (ReString s) = ("\"" ++) . (++ "\"") . concat . (show <$>) $ s

toTrieSameAsDeriv :: Regex ReChar -> ReString -> Property
toTrieSameAsDeriv r (ReString s) = Regex.contains r s === Trie.contains (toTrie r) s

main :: IO ()
main = quickCheck toTrieSameAsDeriv
