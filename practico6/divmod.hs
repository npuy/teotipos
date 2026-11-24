module Divmod where

import qualified Prelude

__ :: any
__ = Prelude.error "Logical or arity value used"

data Nat =
   O
 | S Nat

nat_rec :: a1 -> (Nat -> a1 -> a1) -> Nat -> a1
nat_rec o s n =
  case n of {
   O -> o;
   S n0 -> s n0 (nat_rec o s n0)}

type Sig a = a
  -- singleton inductive, whose constructor was exist
  
sumbool_rec :: (() -> a1) -> (() -> a1) -> Prelude.Bool -> a1
sumbool_rec left right s =
  case s of {
   Prelude.True -> left __;
   Prelude.False -> right __}

add :: Nat -> Nat -> Nat
add n m =
  case n of {
   O -> m;
   S p -> S (add p m)}

sub :: Nat -> Nat -> Nat
sub n m =
  case n of {
   O -> n;
   S k -> case m of {
           O -> n;
           S l -> sub k l}}

le_lt_dec :: Nat -> Nat -> Prelude.Bool
le_lt_dec n m =
  nat_rec (\_ -> Prelude.True) (\_ iHn m0 ->
    case m0 of {
     O -> Prelude.False;
     S n0 -> sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False) (iHn n0)})
    n m

le_gt_dec :: Nat -> Nat -> Prelude.Bool
le_gt_dec =
  le_lt_dec

le_dec :: Nat -> Nat -> Prelude.Bool
le_dec =
  le_gt_dec

lt_dec :: Nat -> Nat -> Prelude.Bool
lt_dec n m =
  le_dec (S n) m

nat_div_mod :: Nat -> Nat -> ((,) Nat Nat)
nat_div_mod a b =
  nat_rec ((,) O O) (\_ iHa ->
    case iHa of {
     (,) n n0 ->
      let {s = lt_dec n0 (sub b (S O))} in
      case s of {
       Prelude.True -> (,) n (add n0 (S O));
       Prelude.False -> (,) (add n (S O)) O}})
    a

