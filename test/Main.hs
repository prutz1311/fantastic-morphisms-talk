module Main where

import Test.Tasty
import Test.Tasty.QuickCheck
import Test.QuickCheck ()
import qualified Test.QuickCheck.Monadic as QM
import Test.QuickCheck.Instances.Natural ()
import Test.Tasty.HUnit as HU
import Numeric.Natural
import Data.List (foldl', sort)
import Data.List.Extra (merge)
import qualified Data.Map.Strict as Map
import qualified Data.Array as A

import RecursionSchemes

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests" 
  [ testProperty "factorial" factorialP
  , testCase "prog p1" progCase
  , testProperty "mergeAnaInt" (mergeAnaP @Int)
  , testProperty "zipAnaIntString" (zipAnaP @Int @String)
  , testProperty "zipAnaWordChar" (zipAnaP @Word @Char)
  , testProperty "scanlAnaSum" (scanlAnaP @Int @Int (+))
  , testProperty "scanlAnaString" (scanlAnaP @Char @[Char] ((\reversedString nextChar -> nextChar : reversedString)))
  , testProperty "qsortHyloInt" (qsortHyloP @Int)
  , testProperty "accuFoldl'List" (accuFoldl'P @Char @[Char] (flip (:)))
  , testProperty "accuScanlSum" (accuScanlP @Int @Int (+))
  , testProperty "accuScanlString" (accuScanlP @Char @[Char] ((\reversedString nextChar -> nextChar : reversedString)))
  , testProperty "perfectZygo" perfectZygoP
  , testProperty "fib" fibP
  , testProperty "rodCuttingDyna" (rodCuttingDynaP rodSamplePrices)
  , testProperty "rodCuttingHisto" (rodCuttingHistoP rodSamplePrices)
  , testProperty "lisHistoInt" (lisHistoP @Int)
  , testProperty "rldFutu" (rldFutuP @Int)
  ]

factorialP :: Natural -> Bool
factorialP n = factorialFix n == referenceFactorial n

progCase :: Assertion
progCase = interpCata p1 (Map.fromList [(0, 100)]) @?= 100

mergeAnaP :: forall a. Ord a => SortedList a -> SortedList a -> Bool
mergeAnaP (Sorted xs) (Sorted ys) = mergeAna (xs, ys) == merge xs ys

zipAnaP :: forall a b. (Eq a, Eq b) => [a] -> [b] -> Bool
zipAnaP as bs = zipAna (as, bs) == zip as bs

scanlAnaP :: forall a b. Eq b => (b -> a -> b) -> b -> [a] -> Bool
scanlAnaP f binitial list = scanlAna f binitial list == scanl f binitial list

qsortHyloP :: forall a. Ord a => [a] -> Bool
qsortHyloP xs = qsortHylo xs == sort xs

accuFoldl'P :: forall a b. Eq b => (b -> a -> b) -> b -> [a] -> Bool
accuFoldl'P f initial list = accuFoldl' f initial list == foldl' f initial list

accuScanlP :: forall a b. Eq b => (b -> a -> b) -> b -> [a] -> Bool
accuScanlP f initial list = accuScanl f initial list == scanl f initial list

perfectZygoP :: Positive Integer -> Property
perfectZygoP (Positive n) = n > 0 && n < 20 ==> QM.monadicIO $ do
  tree <- QM.run (ranTree n)
  QM.assert (perfectZygo tree)

fibP :: Natural -> Property
fibP n = n <= 25 ==> fib n == referenceFib n

rodCuttingDynaP :: A.Array Natural Natural -> Positive Natural -> Property
rodCuttingDynaP prices (Positive len) = len <= 25 ==> rodCuttingDyna prices len == badRodCutting prices len

rodCuttingHistoP :: A.Array Natural Natural -> Positive Natural -> Property
rodCuttingHistoP prices (Positive len) = len <= 25 ==> rodCuttingHisto prices len == badRodCutting prices len

lisHistoP :: forall a. Ord a => [a] -> Bool
lisHistoP xs = lisHisto xs == lis xs

rldFutuP :: forall a. Ord a => [(Positive Int, a)] -> Bool
rldFutuP wrappedCodes =
  let codes = map (\(Positive len, a) -> (len, a)) wrappedCodes
  in rldFutu codes == referenceRld codes
