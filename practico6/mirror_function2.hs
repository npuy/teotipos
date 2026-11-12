module Mirror_function2 where

import qualified Prelude

type Sig a = a
  -- singleton inductive, whose constructor was exist
  
data Bintree a =
   BintreeNil
 | BintreeCons a (Bintree a) (Bintree a)

inverse :: (Bintree a1) -> Bintree a1
inverse b =
  case b of {
   BintreeNil -> BintreeNil;
   BintreeCons x b1 b2 -> BintreeCons x (inverse b2) (inverse b1)}

mirrorC2 :: (Bintree a1) -> (Bintree a1)
mirrorC2 =
  inverse

