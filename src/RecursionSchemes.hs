module RecursionSchemes where

import Control.Monad
import Control.Comonad
import Control.Comonad.Cofree
import Control.Monad.Free
import qualified Data.Array as A
import Data.Bifunctor
import Data.Functor.Foldable hiding (mana)
import Data.Function
import Data.List
import Data.Fix (Fix(..))
import Data.Word
import Numeric.Natural
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import System.Random

referenceFactorial :: Natural -> Natural
referenceFactorial = \n -> if n == 0 then 1 else n * referenceFactorial (n - 1)
-- referenceFactorial = \n -> if n == 0 then 1 else n * ((\n -> if n == 0 then 1 else n * referenceFactorial (n - 1)) (n - 1))
-- referenceFactorial = \n -> if n == 0 then 1 else n * ((\n -> if n == 0 then 1 else n * (\n -> if n == 0 then 1 else n * referenceFactorial (n - 1)) (n - 1)) (n - 1))

referenceRepeat :: forall a. a -> [a]
referenceRepeat = \a -> a : referenceRepeat a
-- referenceRepeat = \a -> a : (\a -> a : referenceRepeat a) a
-- referenceRepeat = \a -> a : (\a -> a : (\a -> a : referenceRepeat a) a) a

-- Pattern : x = expr x -> x = expr (expr x) -> x = expr (expr (expr x)) -> ...
-- captured by Data.Function.fix (as well as monadic and comonadic variants):
--
-- fix :: (a -> a) -> a
-- fix expr = let x = expr x in x
-- 
-- Its usage is commonly referred to as "tying the knot"

factorialFix :: Natural -> Natural
factorialFix =
  let factF :: (Natural -> Natural) -> Natural -> Natural
      factF expr n = if n == 0 then 1 else n * expr (n - 1)
  in fix factF

repeatFix :: forall a. a -> [a]
repeatFix =
  let repeatF :: (a -> [a]) -> a -> [a]
      repeatF expr a = a : expr a
  in fix repeatF

data BTreeF a x
  = Empty
  | Node x a x
  deriving stock (Eq, Ord, Show)

instance Functor (BTreeF a) where
  fmap :: forall x y. (x -> y) -> BTreeF a x -> BTreeF a y
  fmap _ Empty = Empty
  fmap f (Node l a r) = Node (f l) a (f r)

btreeSize :: forall a. Fix (BTreeF a) -> Int
btreeSize =
  let alg :: BTreeF a Int -> Int
      alg Empty        = 0
      alg (Node l _ r) = l + 1 + r
  in cata alg

data ProgF s a x
  = Ret a
  | Put (Int, s) x
  | Get Int (s -> x)

instance Functor (ProgF s a) where
  fmap :: forall x y. (x -> y) -> ProgF s a x -> ProgF s a y
  fmap _ (Ret a) = Ret a
  fmap f (Put (i, x) k) = Put (i, x) (f k)
  fmap f (Get i kf) = Get i (f . kf)
--  fmap f (Get i kf) = Get i (\s -> f (kf s))
--  fmap f (Get i kf) = Get i (fmap f kf)

-- Extensible effects (freer monads)?
-- data Prog s m x where
--   Ret :: a -> Prog s m a
--   Put :: Int -> s -> Prog s m ()
--   Get :: Int -> Prog s m s

-- Free monads?
-- data ProgF s x
--   = Put (Int, s) x
--   | Get Int (s -> x)
-- type Prog s = Free (ProgF s)    -- gives `do` syntax
-- interpFree :: Free (ProgF s) a -> Reader (Map Int s) a
-- interpFree =
--   let alg (CMTF.Pure a) = return a
--       alg (CMTF.Free (Put (i, x) rest) -> local (Map.insert i x) rest
--       alg (CMTF.Free (Get i k)) = asks (Map.! i) >>= k
--   in cata alg

p1 :: Fix (ProgF Int Int)
p1 = Fix (Get 0 (\s -> Fix (Put (0, s + 1) (Fix (Ret s)))))

-- Fix (ProgF s a) -> Writer [String] a
interpCata :: forall s a. Fix (ProgF s a) -> Map Int s -> a
interpCata =
  let alg :: ProgF s a (Map Int s -> a) -> Map Int s -> a
      alg (Ret a)         = \_ -> a
      alg (Put (i, x) k)  = \m -> k (Map.insert i x m)
      alg (Get i kf)      = \m -> kf (m Map.! i) m
  in cata alg

-- interpReader (Ret a) = return a
-- interpReader (Put i x) = local (\m -> Map.insert i m x)
-- interpReader (Get i) = Map.lookup i . ask

mergeAna :: forall a. Ord a => ([a], [a]) -> [a]
mergeAna =
  let coalg :: ([a], [a]) -> ListF a ([a], [a])
      coalg ([]  , []  ) = Nil
      coalg (x:xs, []  ) = Cons x (xs, [])
      coalg ([]  , y:ys) = Cons y ([], ys)
      coalg (x:xs, y:ys) | x < y     = Cons x (xs, y:ys)
                         | otherwise = Cons y (x:xs, ys)
  in ana coalg

zipAna :: forall a b. ([a], [b]) -> [(a, b)]
zipAna =
  let coalg :: ([a], [b]) -> ListF (a, b) ([a], [b])
      coalg ([], _) = Nil
      coalg (_, []) = Nil
      coalg (x:xs, y:ys) = Cons (x, y) (xs, ys)
  in ana coalg

scanlAna :: forall a b. (b -> a -> b) -> b -> [a] -> [b]
scanlAna f binitial list =
  let coalg :: (b, [a]) -> ListF b (b, [a])
      coalg (_, []  ) = Nil
      coalg (b, a:as) = let nextb = f b a in Cons nextb (nextb, as)
  in binitial : ana coalg (binitial, list)

qsortHylo :: forall a. Ord a => [a] -> [a]
qsortHylo =
  let alg :: BTreeF a [a] -> [a]
      alg Empty        = []
      alg (Node l x r) = l ++ [x] ++ r
      coalg :: [a] -> BTreeF a [a]
      coalg []     = Empty
      coalg (a:as) =
        let (l, r) = partition (< a) as
        in Node l a r
  in hylo alg coalg

accu :: forall t a p. Recursive t
                   => (forall x. Base t x -> p -> Base t (x, p)) -- ^ strategy
                   -> (Base t a -> p -> a)                       -- ^ algebra
                   -> t                                          -- ^ structure
                   -> p                                          -- ^ root label
                   -> a
accu st alg t p = alg (fmap (uncurry (accu st alg)) (st (project t) p)) p
-- Compare with `cata alg t = alg (fmap (cata alg) (project t))`
-- (st (project t) p) :: Base t (t, p) - top-level node with branches
--                                       annotated with accumulator values
-- (uncurry (accu st alg)) :: (t, p) -> a - the whole thing being defined
--                                          will be applied
--                                          to subtrees pointed by these
--                                          annotated branches recursively
-- After `fmap ...` we have a `Base t a` - the root node (level)
-- containing results `a` of folding subtrees (just like in a regular `cata`)
-- As the final step `alg (...) p` takes that root node and the root label
-- and performs the final folding calculation

-- interpAccu :: forall s a. Fix (ProgF s a) -> Map Int s -> (a, Map Int s)
interpAccu :: forall s a. Fix (ProgF s a) -> Map Int s -> a
interpAccu =
  let st :: forall x. ProgF s a x -> Map Int s -> ProgF s a (x, Map Int s)
      st (Ret a)        _ = Ret a
      st (Put (i, x) k) m = Put (i, x) (k, Map.insert i x m)
      st (Get i k)      m = Get i (flip (,) m . k)
      alg :: ProgF s a a -> Map Int s -> a
      alg (Ret a)    _ = a
      alg (Put _ k)  _ = k  -- k is a thunk `accu st alg someMap someSubtree`
      alg (Get i kf) m = kf (m Map.! i) -- same: evaluates to `accu st alg someMap someSubtree`
  in accu st alg

-- interpState (Ret a) = return a
-- interpState (Put i x) = modify' (\m -> Map.insert i m x)
-- interpState (Get i) = fmap (Map.! i) get

accuFoldl :: forall a b. (b -> a -> b) -> b -> [a] -> b
accuFoldl f initial list =
  let st :: forall x. ListF a x -> b -> ListF a (x, b)
      st Nil        _ = Nil
      st (Cons a x) b = Cons a (x, (f b a))
      alg :: ListF a b -> b -> b
      alg Nil        accval = accval
      alg (Cons _ b) _      = b
  in accu st alg list initial

accuFoldl' :: forall a b. (b -> a -> b) -> b -> [a] -> b
accuFoldl' f initial list =
  let st :: forall x. ListF a x -> b -> ListF a (x, b)
      st Nil        _ = Nil
      st (Cons a x) b = let nextState = f b a in nextState `seq` Cons a (x, nextState)
      alg :: ListF a b -> b -> b
      alg Nil        accval = accval
      alg (Cons _ b) _      = b
  in accu st alg list initial

accuScanl :: forall a b. (b -> a -> b) -> b -> [a] -> [b]
accuScanl f initial list =
  let st :: forall x. ListF a x -> b -> ListF a (x, b)
      st Nil        _ = Nil
      st (Cons a x) b = Cons a (x, (f b a))
      alg :: ListF a [b] -> b -> [b]
      alg Nil              accval = accval : []
      alg (Cons _ accvals) accval = accval : accvals
  in accu st alg list initial

accuScanl' :: forall a b. (b -> a -> b) -> b -> [a] -> [b]
accuScanl' f initial list =
  let st :: forall x. ListF a x -> b -> ListF a (x, b)
      st Nil        _ = Nil
      st (Cons a x) b = let nextState = f b a in nextState `seq` Cons a (x, nextState)
      alg :: ListF a [b] -> b -> [b]
      alg Nil              accval = accval : []
      alg (Cons _ accvals) accval = accval : accvals
  in accu st alg list initial

relabel :: Fix (BTreeF Integer) -> Integer -> Fix (BTreeF Integer)
relabel tree initial =
  let alg :: BTreeF Integer (Fix (BTreeF Integer)) -> Integer -> Fix (BTreeF Integer)
      alg Empty _ = Fix Empty
      alg (Node l _ r) s = Fix (Node l s r)
      st :: forall x. BTreeF Integer x -> Integer -> BTreeF Integer (x, Integer)
      st Empty _s = Empty
      st (Node l e r) s = let s' = s + e in Node (l, s') e (r, s')
  in accu st alg tree initial

-- mutu :: forall t a b. (Base t (a, b) -> a) -> (Base t (a, b) -> b) -> (t -> a, t -> b)
-- mutu alg1 alg2 = (fst . h, snd . h)
--   where h = cata alg
--         alg x = (alg1 x, alg2 x)

primes :: [Integer]
primes = sieve (2 : [3, 5..])
  where sieve (p:xs) = p : sieve [x|x <- xs, x `mod` p > 0]
        sieve [] = error "unreachable"

getExponent :: Integer -> Integer -> Integer
getExponent factor n = go 0 n
  where go acc x = let (d, m) = x `divMod` factor
                   in if m == 0 then go (acc + 1) d else acc 

factorize :: Integer -> Integer -> [Integer]
factorize upper n = map (flip getExponent n) (takeWhile (<= upper) primes)

factorize11 :: Integer -> (Integer, Integer, Integer, Integer, Integer)
factorize11 n = case factorize 11 n of
  [e2, e3, e5, e7, e11] -> (e2, e3, e5, e7, e11)
  _ -> error "unreachable"

encLit :: Integer -> Integer
encLit n = if n >= 0 then 2 * n + 1 else 2 * (- n)

decLit :: Integer -> Integer
decLit n =
  let (d, m) = n `divMod` 2
  in if m == 0 then negate d else d

newtype Fix1 f g = Fix1 { unFix1 :: f (Fix1 f g) (Fix2 f g) }
newtype Fix2 f g = Fix2 { unFix2 :: g (Fix1 f g) (Fix2 f g) }

comutu :: forall f g c. (Bifunctor f, Bifunctor g)
       => (c -> f c c) 
       -> (c -> g c c)
       -> c
       -> (Fix1 f g, Fix2 f g)
comutu coalg1 coalg2 seed =
  let x :: c -> Fix1 f g
      x = Fix1 . bimap x y . coalg1
      y :: c -> Fix2 f g
      y = Fix2 . bimap x y . coalg2
  in (x seed, y seed)

data ExprF e t = Add' e t | Minus' e t | FromT' t deriving (Show)
data TermF e t = Lit' t | Neg' t | Paren' e deriving (Show)

-- `Functor` is required for `Bifunctor`
instance Functor (ExprF e) where
  fmap :: forall a b. (a -> b) -> ExprF e a -> ExprF e b
  fmap f (Add' e t) = Add' e (f t)
  fmap f (Minus' e t) = Minus' e (f t)
  fmap f (FromT' t) = FromT' (f t)

instance Functor (TermF e) where
  fmap :: forall a b. (a -> b) -> TermF e a -> TermF e b
  fmap f (Lit' t) = Lit' (f t)
  fmap f (Neg' t) = Neg' (f t)
  fmap _ (Paren' e) = Paren' e

instance Bifunctor ExprF where
  bimap :: forall e1 e2 t1 t2. (e1 -> e2) -> (t1 -> t2)
                            -> ExprF e1 t1 -> ExprF e2 t2
  bimap f g (Add' e t) = Add' (f e) (g t)
  bimap f g (Minus' e t) = Minus' (f e) (g t)
  bimap _ g (FromT' t) = FromT' (g t)

instance Bifunctor TermF where
  bimap :: forall e1 e2 t1 t2. (e1 -> e2) -> (t1 -> t2)
                            -> TermF e1 t1 -> TermF e2 t2
  bimap _ g (Lit' t) = Lit' (g t)
  bimap _ g (Neg' t) = Neg' (g t)
  bimap f _ (Paren' e) = Paren' (f e)

genExpr :: Integer -> ExprF Integer Integer
genExpr n =
  let (e2, e3, e5, e7, e11) = factorize11 n
  in if e2 > 0 || e3 > 0
     then Add' e2 e3
     else if e5 > 0 || e7 > 0
          then Minus' e5 e7
          else FromT' e11

genTerm :: Integer -> TermF Integer Integer
genTerm n =
  let (e2, e3, e5, _, _) = factorize11 n
  in if e2 > 0
     then Lit' (decLit e2)
     else if e3 > 0
          then Neg' e3
          else Paren' e5

decExprTerm :: Integer -> (Fix1 ExprF TermF, Fix2 ExprF TermF)
decExprTerm = comutu genExpr genTerm

-- maphd f list = case list of { [] -> []; x : xs -> f x : xs }
-- maphd f list = over _head f list
maphdApo :: forall a. (a -> a) -> [a] -> [a]
maphdApo f =
  let coalg :: [a] -> ListF a (Either [a] [a])
      coalg [] = Nil
      coalg (x:xs) = Cons (f x) (Left xs)
  in apo coalg

insertApo :: forall a. Ord a => a -> [a] -> [a]
insertApo y =
  let coalg :: [a] -> ListF a (Either [a] [a])
      coalg []                     = Cons y (Left [])
      coalg xxs@(x:xs) | y <= x    = Cons y (Left xxs)
                       | otherwise = Cons x (Right xs)
  in apo coalg
 
perfectZygo :: forall a. Fix (BTreeF a) -> Bool
perfectZygo =
  let p :: BTreeF a (Integer, Bool) -> Bool
      p Empty                      = True
      p (Node (dl, pl) _ (dr, pr)) = pl && pr && dl == dr
      d :: BTreeF a Integer -> Integer
      d Empty          = 0
      d (Node dl _ dr) = 1 + max dl dr
  in zygo d p

myHisto :: forall t a. Recursive t => (Base t (Cofree (Base t) a) -> a) -> t -> a
myHisto alg =
  let alg' :: Base t (Cofree (Base t) a) -> Cofree (Base t) a
      alg' x = alg x :< x
  in extract @(Cofree (Base t)) . cata @t @(Cofree (Base t) a) alg'

-- Dynamic programming
dyna :: forall f a c. Functor f
     => (f (Cofree f a) -> a)
     -> (c -> f c)
     -> c
     -> a
dyna alg coalg =
  let alg' :: f (Cofree f a) -> Cofree f a
      alg' x = alg x :< x
  in extract . hylo @f @(Cofree f a) @c alg' coalg

-- Recomputes `referenceFib (n - 1)` and `referenceFib (n - 2)`
-- from scratch every time: runs in exponential time
referenceFib :: Natural -> Natural
referenceFib 0 = 1
referenceFib 1 = 1
referenceFib n = referenceFib (n - 1) + referenceFib (n - 2)

-- When dealing with integer inputs where the integer represents
-- the size of the problem a good functor choice is `Maybe`:
-- `Nothing` represents a base case, `Just (n - 1)` represents
-- a subproblem of size `n-1`, and solutions to all the other
-- subproblems are found in the `Maybe (Cofree Maybe a)`
-- datastructure passed to the coalgebra

-- data Nat = Zero | Succ Nat
-- Nat ~ Fix (Maybe)
fib :: Natural -> Natural
fib =
  let alg :: Maybe (Cofree Maybe Natural) -> Natural
      alg Nothing = 1
      alg (Just (rm1 :< mb2)) = rm1 + case mb2 of { Nothing -> 1; Just (rm2 :< _) -> rm2 }
      coalg :: Natural -> Maybe Natural
      coalg 0 = Nothing
      coalg 1 = Nothing
      coalg n = Just (n - 1)
  in dyna alg coalg

rodSamplePrices :: A.Array Natural Natural
rodSamplePrices = A.listArray (1, 10) [1, 5, 8, 9, 10, 17, 17, 20, 24, 30]

lookUpPrice :: A.Array Natural Natural -> Natural -> Natural
lookUpPrice prices l =
  let maxlen = snd (A.bounds prices)
  in prices A.! min l maxlen

badRodCutting :: A.Array Natural Natural -> Natural -> Natural
badRodCutting prices 1   = lookUpPrice prices 1
badRodCutting prices len =
  maximum (lookUpPrice prices len :
           map (\toCutOff -> lookUpPrice prices toCutOff + badRodCutting prices (len - toCutOff)) [1..(len-1)])

cfmToList :: forall a. Maybe (Cofree Maybe a) -> [a]
cfmToList = ana (\m -> case m of { Nothing -> Nil; Just (a :< ma) -> Cons a ma })
-- cfmToList x = case x of { Nothing -> []; Just (a :< ma) -> a : cfmToList ma }

listToCfm :: forall a. [a] -> Maybe (Cofree Maybe a)
listToCfm = cata (\lf -> case lf of { Nil -> Nothing; Cons a ma -> Just (a :< ma) })

rodCuttingAlg :: A.Array Natural Natural -> Maybe (Cofree Maybe Natural) -> Natural
rodCuttingAlg prices Nothing = lookUpPrice prices 1
rodCuttingAlg prices cfm     =
  let subsolutions = cfmToList cfm
      lengthm1 = fromIntegral (length subsolutions)
      thisRodPrice = lookUpPrice prices (lengthm1 + 1)
  in maximum (thisRodPrice :
              map (\(toCutOff, otherPieceRevenue) -> lookUpPrice prices toCutOff + otherPieceRevenue)
                  (zip [1..lengthm1] subsolutions))

rodCuttingDyna :: A.Array Natural Natural -> Natural -> Natural
rodCuttingDyna prices len =
  let coalg :: Natural -> Maybe Natural
      coalg 1 = Nothing
      coalg n = Just (n - 1)
  in dyna (rodCuttingAlg prices) coalg len

rodCuttingHisto :: A.Array Natural Natural -> Natural -> Natural
rodCuttingHisto prices len = histo (rodCuttingAlg prices) (len - 1)

lis :: forall a. Ord a => [a] -> Natural
lis = snd . lis'

lis' :: forall a. Ord a => [a] -> (Natural, Natural)
lis' [] = (0, 0)
lis' (x : xs) = (a, b)
  where a = 1 + maximum [fst (lis' sub) | sub <- tails xs, null sub || x < head sub]
        b = max a (snd (lis' xs))

findNext :: forall a. Ord a => a -> Cofree (ListF a) (Natural, Natural) -> Natural
findNext _ ((a, _) :< Nil          ) = a
findNext x ((a, _) :< Cons y table') = if x < y then max a b else b
  where b = findNext x table'

lisHisto :: forall a. Ord a => [a] -> Natural
lisHisto =
  let alg :: ListF a (Cofree (ListF a) (Natural, Natural)) -> (Natural, Natural)
      alg Nil = (0, 0)
      alg (Cons x table) =
        let a = 1 + findNext x table
            b = max a (snd (extract table))
        in (a, b)
  in snd . histo alg

-- Run-length decoding
-- referenceRld [(4, 'x'), (2, 'y')] == "xxxxyy"
referenceRld :: forall a. [(Int, a)] -> [a]
referenceRld codes = concatMap (\(n, x) -> replicate n x) codes

rldAna :: forall a. [(Int, a)] -> [a]
rldAna =
  let coalg :: [(Int, a)] -> ListF a [(Int, a)]
      coalg [] = Nil
      coalg ((n, x):xs) | n == 1 = Cons x xs
                        | otherwise = Cons x ((n - 1, x):xs)
  in ana coalg

-- futu :: forall t a. Corecursive t => (a -> Base t (Free (Base t) a)) -> a -> t
rldFutu :: forall a. [(Int, a)] -> [a]
rldFutu =
  let dec :: [(Int, a)] -> ListF a (Free (ListF a) [(Int, a)])
      dec [] = Nil
      dec ((n, c) : xs) =
        let rep 0 = Pure xs
            rep m = Free (Cons c (rep (m - 1)))
            -- Free g = rep n
        in case rep n of
          Pure _ -> error "unreachable: had length of 0 in RLE"
          Free g -> g
  in futu dec

myFutu :: forall t a. Corecursive t => (a -> Base t (Free (Base t) a)) -> a -> t
myFutu coalg = ana coalg' . Pure
  where coalg' :: Free (Base t) a -> Base t (Free (Base t) a)
        coalg' (Pure a) = coalg a
        coalg' (Free k) = k

-- Monadic catamorphism
-- cataA = cata?
mcata :: forall t m a. (Recursive t, Monad m)
      => (forall x. Base t (m x) -> m (Base t x))  -- `sequence` or `sequenceA`-like function
      -> (Base t a -> m a)
      -> t
      -> m a
mcata seq_ alg = cata (seq_ >=> alg)

mhylo :: forall f m a c. (Monad m, Functor f)
      => (forall x. f (m x) -> m (f x))
      -> (f a -> m a)
      -> (c -> m (f c))
      -> c
      -> m a
mhylo seq_ alg coalg = coalg >=> seq_ . fmap (mhylo seq_ alg coalg) >=> alg

mana :: forall t m c. (Monad m, Corecursive t)
     => (forall x. Base t (m x) -> m (Base t x))
     -> (c -> m (Base t c))
     -> c
     -> m t
mana seq_ coalg = mhylo seq_ (return . embed) coalg

lToR :: forall m a x. Monad m => BTreeF a (m x) -> m (BTreeF a x)
lToR Empty          = pure Empty
lToR (Node ml a mr) = Node <$> ml <*> pure a <*> mr

ranTree :: Integer -> IO (Fix (BTreeF Word8))
ranTree =
  let gen :: Integer -> IO (BTreeF Word8 Integer)
      gen 0 = return Empty
      gen n = fmap (\a -> Node (n - 1) a (n - 1)) randomIO
  in mana lToR gen
