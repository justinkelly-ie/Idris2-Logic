module Singleton.Interfaces

import Data.Vect
import Data.Linear
import Math.Interfaces
import Singleton.Bit
import Math.Sing

%default total

-----------------------------------------------------------------------
-- BRIDGE UTILITIES
-----------------------------------------------------------------------

||| Converts a list of BVals to Integers.
public export
bvalsToIntegers : List BVal -> List Integer
bvalsToIntegers [] = []
bvalsToIntegers (ZeroS :: xs) = 0 :: bvalsToIntegers xs
bvalsToIntegers (OneS () n :: xs) = n :: bvalsToIntegers xs
bvalsToIntegers (_ :: xs) = 0 :: bvalsToIntegers xs

||| Converts a list of Integers to BVals (mod 2).
public export
integersToBVals : List Integer -> List BVal
integersToBVals [] = []
integersToBVals (n :: xs) =
  (if mod n 2 == 0 then Zero else One) :: integersToBVals xs

||| Linear consumption of a Vect of BVals.
public export
lconsumeVect : {n : Nat} -> (1 _ : Vect n BVal) -> ()
lconsumeVect [] = ()
lconsumeVect (x :: xs) = case lconsume x of () => lconsumeVect xs

||| Linear duplication of a Vect of BVals.
public export
lcomultVect : {n : Nat} -> (1 _ : Vect n BVal) -> LPair (Vect n BVal) (Vect n BVal)
lcomultVect [] = Builtin.(#) [] []
lcomultVect (x :: xs) =
  let Builtin.(#) x1 x2 = lcomult x
      Builtin.(#) xs1 xs2 = lcomultVect xs
  in Builtin.(#) (x1 :: xs1) (x2 :: xs2)
