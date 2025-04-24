{-# OPTIONS_GHC -Wno-unused-foralls #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}

module Plutarch.Internal.TermCont (
  hashOpenTerm,
  TermCont (TermCont),
  runTermCont,
  unTermCont,
  tcont,
  pfindPlaceholder,
  pfindPlaceholders,
  pfindPlaceholderSet,
) where

import Data.IntSet (IntSet)
import Data.IntSet qualified as IntSet
import Data.Kind (Type)
import Data.List (foldl', transpose, (\\))
import Data.String (fromString)
import Plutarch.Internal.Term (Config (Tracing), Dig, HoistedTerm (..), PType,
                               RawTerm (..), S, Term (Term),
                               TracingMode (DetTracing), asRawTerm, getTerm,
                               hashRawTerm, perror, pgetConfig)
import Plutarch.Internal.Trace (ptraceInfo)

newtype TermCont :: forall (r :: PType). S -> Type -> Type where
  TermCont :: forall r s a. {runTermCont :: (a -> Term s r) -> Term s r} -> TermCont @r s a

unTermCont :: TermCont @a s (Term s a) -> Term s a
unTermCont t = runTermCont t id

instance Functor (TermCont s) where
  fmap f (TermCont g) = TermCont $ \h -> g (h . f)

instance Applicative (TermCont s) where
  pure x = TermCont $ \f -> f x
  x <*> y = do
    x <- x
    x <$> y

instance Monad (TermCont s) where
  (TermCont f) >>= g = TermCont $ \h ->
    f
      ( \x ->
          runTermCont (g x) h
      )

instance MonadFail (TermCont s) where
  fail s = TermCont $ \_ ->
    pgetConfig $ \case
      -- Note: This currently works because DetTracing is the most specific
      -- tracing mode.
      Tracing _ DetTracing -> ptraceInfo "Pattern matching failure in TermCont" perror
      _ -> ptraceInfo (fromString s) perror

tcont :: ((a -> Term s r) -> Term s r) -> TermCont @r s a
tcont = TermCont

hashOpenTerm :: Term s a -> TermCont s Dig
hashOpenTerm x = TermCont $ \f -> Term $ \i -> do
  y <- asRawTerm x i
  asRawTerm (f . hashRawTerm . getTerm $ y) i

-- This can technically be done outside of TermCont.
-- Need to pay close attention when killing branch with this.
-- If term is pre-evaluated (via `evalTerm`), RawTerm will no longer hold
-- tagged RPlaceholder.

{- | Given a term, and an integer tag, this function checks if the term holds and
@PPlaceholder@ with the given integer tag.
-}
pfindPlaceholder :: Integer -> Term s a -> TermCont s Bool
pfindPlaceholder idx x = TermCont $ \f -> Term $ \i -> do
  y <- asRawTerm x i

  let
    findPlaceholder (RLamAbs _ x) = findPlaceholder x
    findPlaceholder (RApply x xs) = any findPlaceholder (x : xs)
    findPlaceholder (RForce x) = findPlaceholder x
    findPlaceholder (RDelay x) = findPlaceholder x
    findPlaceholder (RHoisted (HoistedTerm _ x)) = findPlaceholder x
    findPlaceholder (RPlaceHolder idx') = idx == idx'
    findPlaceholder (RConstr _ xs) = any findPlaceholder xs
    findPlaceholder (RCase x xs) = any findPlaceholder (x : xs)
    findPlaceholder (RVar _) = False
    findPlaceholder (RConstant _) = False
    findPlaceholder (RBuiltin _) = False
    findPlaceholder (RCompiled _) = False
    findPlaceholder RError = False

  asRawTerm (f . findPlaceholder . getTerm $ y) i

-- | Tries to find all idxs in one go, otherwise 'pfindPlaceholder'.

pfindPlaceholders :: [Integer] -> Term s a -> TermCont s [Bool]
pfindPlaceholders idxs x = TermCont $ \f -> Term $ \i -> do
  y <- asRawTerm x i
  let
    l = length idxs
    conv :: [RawTerm] -> [Bool]
    -- TODO: (choener) Consider recursively dropping idxs that have been found, and splicing them
    -- back in. Or just returning only those idxs that have been found?
    conv = map or . transpose . map findPlaceholders
    findPlaceholders (RLamAbs _ x) = findPlaceholders x
    findPlaceholders (RApply x xs) = conv (x:xs)
    findPlaceholders (RForce x)= findPlaceholders x
    findPlaceholders (RDelay x)= findPlaceholders x
    findPlaceholders (RHoisted (HoistedTerm _ x)) = findPlaceholders x
    findPlaceholders (RPlaceHolder idx') = map (idx'==) idxs
    findPlaceholders (RConstr _ xs) = conv xs
    findPlaceholders (RCase x xs) = conv (x:xs)
    findPlaceholders (RVar _) = replicate l False
    findPlaceholders (RConstant _) = replicate l False
    findPlaceholders (RBuiltin _) = replicate l False
    findPlaceholders (RCompiled _) = replicate l False
    findPlaceholders RError = replicate l False
  asRawTerm (f . findPlaceholders . getTerm $ y) i

-- | Tries to find all idxs in one go, otherwise 'pfindPlaceholder'.
--
-- This function is not faster than 'pfindPlaceholders', but more clean, I'd say.

pfindPlaceholderSet :: IntSet -> Term s a -> TermCont s IntSet
pfindPlaceholderSet idxs x = TermCont $ \f -> Term $ \i -> do
  y <- asRawTerm x i
  let
    go :: (IntSet,IntSet) -> RawTerm -> (IntSet,IntSet)
    go (found,cands) rawTerm =
      let herefound = findPlaceholders cands rawTerm
          nextcands = cands IntSet.\\ herefound
      in  (found `IntSet.union` herefound, nextcands)
    rungo js xs = fst $ foldl' go ([],js) xs
    findPlaceholders js (RLamAbs _ x) = findPlaceholders js x
    findPlaceholders js (RApply x xs) = rungo js (x:xs)
    findPlaceholders js (RForce x)= findPlaceholders js x
    findPlaceholders js (RDelay x)= findPlaceholders js x
    findPlaceholders js (RHoisted (HoistedTerm _ x)) = findPlaceholders js x
    findPlaceholders js (RPlaceHolder (fromIntegral -> idx')) = IntSet.filter (idx'==) js
    findPlaceholders js (RConstr _ xs) = rungo js xs
    findPlaceholders js (RCase x xs) = rungo js (x:xs)
    findPlaceholders  _ (RVar _) = []
    findPlaceholders  _ (RConstant _) = []
    findPlaceholders  _ (RBuiltin _) = []
    findPlaceholders  _ (RCompiled _) = []
    findPlaceholders  _ RError = []
  asRawTerm (f . findPlaceholders idxs . getTerm $ y) i

