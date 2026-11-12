module Mirror_function where

import qualified Prelude

__ :: any
__ = Prelude.error "Logical or arity value used"

type Sig a = a
  -- singleton inductive, whose constructor was exist
  
sig_rec :: (a1 -> () -> a2) -> a1 -> a2
sig_rec exist s =
  exist s __

data Bintree a =
   BintreeNil
 | BintreeCons a (Bintree a) (Bintree a)

bintree_rec :: a2 -> (a1 -> (Bintree a1) -> a2 -> (Bintree a1) -> a2 -> a2)
               -> (Bintree a1) -> a2
bintree_rec bintreeNil bintreeCons b =
  case b of {
   BintreeNil -> bintreeNil;
   BintreeCons a b0 b1 ->
    bintreeCons a b0 (bintree_rec bintreeNil bintreeCons b0) b1
      (bintree_rec bintreeNil bintreeCons b1)}

mirrorC :: (Bintree a1) -> (Bintree a1)
mirrorC t =
  bintree_rec BintreeNil (\a _ iHt1 _ iHt2 ->
    sig_rec (\t1' _ -> sig_rec (\t2' _ -> BintreeCons a t2' t1') iHt2) iHt1)
    t

