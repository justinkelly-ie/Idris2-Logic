module Boole.OnCircuit

import Data.List
import Math.Multiset
import Math.OnSeq.OnMSet
import Boole.Bit
import Boole.Byte
import Boole.Polynumber
import Boole.Circuit

%default total

||| An on-sequence (ongoing sequence) of logical circuits.
public export
0 OnCircuit : Type
OnCircuit = OnSeq Circuit

||| A finite consecutive clip of a circuit sequence.
public export
0 ClipCircuit : Type
ClipCircuit = Clip Circuit

||| Pointwise addition (XOR) of two ongoing circuit sequences.
public export
addOnCircuit : OnCircuit -> OnCircuit -> OnCircuit
addOnCircuit = zipWith addBoolePoly

||| Pointwise multiplication (AND) of two ongoing circuit sequences.
public export
mulOnCircuit : OnCircuit -> OnCircuit -> OnCircuit
mulOnCircuit = zipWith mulBoolePoly

||| Creates a constant variable on-circuit (constant Var k at every step).
public export
varOnCircuit : (k : Nat) -> OnCircuit
varOnCircuit k = constant 0 (Var k)

||| The standard expanding variable sequence [a_n> where term n is variable Var n.
public export
varSequence : OnCircuit
varSequence = MkOnSeq 0 (\n => Var n)

||| Pointwise evaluation of an ongoing circuit sequence at an ongoing assignment sequence.
public export
evalOnCircuit : OnCircuit -> OnSeq (List BVal) -> OnSeq BVal
evalOnCircuit = zipWith evalBoolePoly

-----------------------------------------------------------------------
-- UNBOUNDED LOGIC VARIABLES (OnByte)
-----------------------------------------------------------------------

||| An ongoing byte coordinate (unbounded logic vector) where the length of the vector
||| grows with the sequence index.
public export
0 OnByte : Type
OnByte = OnSeq (List BVal)

||| Pointwise addition (XOR) of two lists of BVals.
public export
addListBVal : List BVal -> List BVal -> List BVal
addListBVal [] ys = ys
addListBVal xs [] = xs
addListBVal (x :: xs) (y :: ys) = addBVal x y :: addListBVal xs ys

||| Pointwise addition of two ongoing byte coordinate sequences.
public export
addOnByte : OnByte -> OnByte -> OnByte
addOnByte = zipWith addListBVal

||| Pointwise multiplication (AND) of two lists of BVals.
public export
mulListBVal : List BVal -> List BVal -> List BVal
mulListBVal [] _ = []
mulListBVal _ [] = []
mulListBVal (x :: xs) (y :: ys) = mulBVal x y :: mulListBVal xs ys

||| Pointwise multiplication of two ongoing byte coordinate sequences.
public export
mulOnByte : OnByte -> OnByte -> OnByte
mulOnByte = zipWith mulListBVal

||| Pointwise check if components are all zero.
public export
isZeroOnByte : OnByte -> OnSeq Bool
isZeroOnByte = map isZeroList
  where
    isZeroList : List BVal -> Bool
    isZeroList [] = True
    isZeroList (Zero :: xs) = isZeroList xs
    isZeroList (One :: _) = False

||| Pointwise check if any component is non-zero.
public export
isNonZeroOnByte : OnByte -> OnSeq Bool
isNonZeroOnByte = map (not . isZeroList)
  where
    isZeroList : List BVal -> Bool
    isZeroList [] = True
    isZeroList (Zero :: xs) = isZeroList xs
    isZeroList (One :: _) = False
