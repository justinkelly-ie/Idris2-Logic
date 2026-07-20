module Logic.Interfaces

import Data.Vect
import Data.Linear
import Math.Interfaces
import Math.Singleton.Bit
import Math.Singleton.Sing
import Math.BoxInt
import Math.Multiset

%default total

-----------------------------------------------------------------------
-- BRIDGE UTILITIES
-----------------------------------------------------------------------

||| Converts a list of Bits to Integers.
public export
bitsToIntegers : List Bit -> List Integer
bitsToIntegers [] = []
bitsToIntegers (x :: xs) = bitToInteger x :: bitsToIntegers xs

||| Converts a list of Integers to Bits (mod 2).
public export
integersToBits : List Integer -> List Bit
integersToBits [] = []
integersToBits (n :: xs) =
  (if mod n 2 == 0 then Zero else One) :: integersToBits xs

||| Linear consumption of a Vect of Bits.
public export
lconsumeVect : {n : Nat} -> (1 _ : Vect n Bit) -> ()
lconsumeVect [] = ()
lconsumeVect (x :: xs) = case lconsume x of () => lconsumeVect xs

||| Linear duplication of a Vect of Bits.
public export
lcomultVect : {n : Nat} -> (1 _ : Vect n Bit) -> LPair (Vect n Bit) (Vect n Bit)
lcomultVect [] = Builtin.(#) [] []
lcomultVect (x :: xs) =
  let Builtin.(#) x1 x2 = lcomult x
      Builtin.(#) xs1 xs2 = lcomultVect xs
  in Builtin.(#) (x1 :: xs1) (x2 :: xs2)
