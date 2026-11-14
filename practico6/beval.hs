module Beval where

import qualified Prelude

data Bool =
   True
 | False

type Sig a = a
  -- singleton inductive, whose constructor was exist
  
type Value = Bool

data BoolExpr =
   Bbool Bool
 | Band BoolExpr BoolExpr
 | Bnot BoolExpr

beval1 :: BoolExpr -> Value
beval1 e =
  case e of {
   Bbool b -> b;
   Band e1 e2 -> case beval1 e1 of {
                  True -> beval1 e2;
                  False -> False};
   Bnot e1 -> case beval1 e1 of {
               True -> False;
               False -> True}}

beval2 :: BoolExpr -> Value
beval2 e =
  case e of {
   Bbool b -> b;
   Band e1 e2 -> case beval2 e1 of {
                  True -> beval2 e2;
                  False -> False};
   Bnot e1 -> case beval2 e1 of {
               True -> False;
               False -> True}}

beval1C :: BoolExpr -> Value
beval1C =
  beval1

beval2C :: BoolExpr -> Value
beval2C =
  beval2

