module Beval_bool where

import qualified Prelude

type Sig a = a
  -- singleton inductive, whose constructor was exist
  
type Value = Prelude.Bool

data BoolExpr =
   Bbool Prelude.Bool
 | Band BoolExpr BoolExpr
 | Bnot BoolExpr

beval1 :: BoolExpr -> Value
beval1 e =
  case e of {
   Bbool b -> b;
   Band e1 e2 ->
    case beval1 e1 of {
     Prelude.True -> beval1 e2;
     Prelude.False -> Prelude.False};
   Bnot e1 ->
    case beval1 e1 of {
     Prelude.True -> Prelude.False;
     Prelude.False -> Prelude.True}}

beval2 :: BoolExpr -> Value
beval2 e =
  case e of {
   Bbool b -> b;
   Band e1 e2 ->
    case beval2 e1 of {
     Prelude.True -> beval2 e2;
     Prelude.False -> Prelude.False};
   Bnot e1 ->
    case beval2 e1 of {
     Prelude.True -> Prelude.False;
     Prelude.False -> Prelude.True}}

beval1C :: BoolExpr -> Value
beval1C =
  beval1

beval2C :: BoolExpr -> Value
beval2C =
  beval2

