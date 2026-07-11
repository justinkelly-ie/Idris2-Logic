module Logic.BooleFunction

import Data.List
import Data.Nat
import Math.Multiset
import Math.Singleton.Sing
import Math.Singleton.Bit
import Math.BoxInt
import Logic.Circuit
import Logic.BoolePolynumber
import Logic.MobiusTransform

%default total

||| A BooleFunction representing a logical mapping from B₂^arity to B₂.
||| Under Norman Wildberger's Algebra of Boole, it is represented by its
||| truth table (a list of 2^arity values in B₂).
public export
record BooleFunction where
  constructor MkBooleFunction
  arity : Nat
  truthTable : List BVal

||| Helper to lookup elements in a list.
public export
lookupIndex : Nat -> List a -> Maybe a
lookupIndex _ [] = Nothing
lookupIndex 0 (x :: _) = Just x
lookupIndex (S k) (_ :: xs) = lookupIndex k xs

||| Converts a binary tuple of BVals (where OneS () 1 is 1 and ZeroS is 0) to a Nat index.
||| e.g. [0, 0] -> 0, [0, 1] -> 1, [1, 0] -> 2, [1, 1] -> 3.
public export
tupleToIndex : List BVal -> Nat
tupleToIndex [] = 0
tupleToIndex (x :: xs) =
  let bit = if x == ZeroS then 0 else 1
  in bit * (power 2 (length xs)) + tupleToIndex xs

||| Evaluate a BooleFunction at a given input tuple.
public export
evaluate : BooleFunction -> List BVal -> BVal
evaluate (MkBooleFunction arity table) inputs =
  let idx = tupleToIndex inputs
  in case lookupIndex idx table of
       Just val => val
       Nothing  => ZeroS

||| Convert a BooleFunction to its unique algebraic BoolePolynumber representation.
||| This uses the Boole-Möbius transform to find the polynumber coefficients.
public export
toPolynumber : BooleFunction -> BoolePolynumber
toPolynumber (MkBooleFunction arity table) =
  let coeffs = mobiusTransform table
  in denseToSparse coeffs

||| Convert a BoolePolynumber back to its truth table BooleFunction representation.
public export
fromPolynumber : (arity : Nat) -> BoolePolynumber -> BooleFunction
fromPolynumber arity poly =
  let denseCoeffs = sparseToDense (power 2 arity) poly
      table = mobiusTransform denseCoeffs
  in MkBooleFunction arity table

||| The constant zero BooleFunction of a given arity.
public export
constantZero : (arity : Nat) -> BooleFunction
constantZero arity =
  let size = power 2 arity
      table = replicate size (the BVal ZeroS)
  in MkBooleFunction arity table

||| The constant one BooleFunction of a given arity.
public export
constantOne : (arity : Nat) -> BooleFunction
constantOne arity =
  let size = power 2 arity
      table = replicate size (OneS () 1)
  in MkBooleFunction arity table

||| The projection BooleFunction returning the value of the i-th variable.
||| Note: varIdx is 0-indexed, where 0 represents the least significant variable.
public export
projection : (arity : Nat) -> (varIdx : Nat) -> BooleFunction
projection arity varIdx =
  let size = power 2 arity
      table = map (\idx => if testBit idx varIdx then OneS () 1 else the BVal ZeroS) [0 .. minus size 1]
  in MkBooleFunction arity table
  where
    testBit : Nat -> Nat -> Bool
    testBit n 0 = (n `mod` 2) == 1
    testBit n (S k) = testBit (n `div` 2) k
