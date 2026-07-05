module Boole.Byte

import Data.List
import public Math.Sing
import public Math.Sing1
import public Math.Vexel
import public Math.DepVexel
import public Math.DepSing
import public Boole.BF2
import public Boole.Bit

%default total

-----------------------------------------------------------------------
-- BOOLE ALGEBRA OVER VEXELS (MULTISETS)
--
-- A Vexel representing logical state inputs/outputs.
-- Defined as a list of singleton bit-gates over BF2.
-----------------------------------------------------------------------

||| A Byte is a one-dimensional logic vector represented as a Vexel BF2 state.
public export
0 Byte : (state : Type) -> Type
Byte state = Vexel BF2 state

||| A dependently typed Byte tracking coordinates at compile time.
public export
0 DepByte : (state : Type) -> (xs : Vexel BF2 state) -> Type
DepByte state xs = DepVexel BF2 state (vexelToMSet xs)

-----------------------------------------------------------------------
-- VECTOR ARITHMETIC
-----------------------------------------------------------------------

||| Pointwise addition (XOR) of two Boole vectors.
public export
addByte : (Eq state) => Byte state -> Byte state -> Byte state
addByte = addVexels

||| Helper to lookup the weight of a state coordinate in a Byte.
public export
lookupWeight : Eq state => state -> Byte state -> BF2
lookupWeight _ [] = Z
lookupWeight x (ZeroS :: rest) = lookupWeight x rest
lookupWeight x (OneS y w :: rest) =
  if x == y then w + lookupWeight x rest else lookupWeight x rest

||| Pointwise multiplication (AND) of two Boole vectors.
public export
mulByte : (Eq state) => Byte state -> Byte state -> Byte state
mulByte [] _ = []
mulByte (ZeroS :: xs) ys = ZeroS :: mulByte xs ys
mulByte (OneS x w1 :: xs) ys =
  let w2 = lookupWeight x ys
      prod = w1 * w2
  in if prod == Z
       then mulByte xs ys
       else OneS x prod :: mulByte xs ys

||| Scalar multiplication: multiply every component by a BF2.
public export
scaleByte : BF2 -> Byte state -> Byte state
scaleByte _ [] = []
scaleByte s (ZeroS :: xs) = ZeroS :: scaleByte s xs
scaleByte s (OneS x w :: xs) =
  let prod = s * w in
  if prod == Z then scaleByte s xs else OneS x prod :: scaleByte s xs

||| The zero vector.
public export
zeroByte : Byte state
zeroByte = []

||| The one vector (all components One) relative to a finite domain of states.
public export
oneByte : List state -> Byte state
oneByte [] = []
oneByte (x :: xs) = OneS x O :: oneByte xs

-----------------------------------------------------------------------
-- PREDICATES
-----------------------------------------------------------------------

||| Test whether a Boole vector is the zero vector.
public export
isZeroByte : Byte state -> Bool
isZeroByte [] = True
isZeroByte (ZeroS :: xs) = isZeroByte xs
isZeroByte (OneS _ w :: xs) = (w == Z) && isZeroByte xs

||| Test whether a Boole vector is nonzero.
public export
isNonZeroByte : Byte state -> Bool
isNonZeroByte v = not (isZeroByte v)

-----------------------------------------------------------------------
-- ARISTOTLE'S FOUR SYLLOGISTIC FORMS
-----------------------------------------------------------------------

||| Every Q is a P: Every active coordinate in Q is active in P.
public export
everyQisP : Eq state => Byte state -> Byte state -> Bool
everyQisP [] _ = True
everyQisP (ZeroS :: xs) ys = everyQisP xs ys
everyQisP (OneS x w :: xs) ys =
  if w == O
  then (lookupWeight x ys == O) && everyQisP xs ys
  else everyQisP xs ys

||| No Q is a P: Q · P = 0.
public export
noQisP : Eq state => Byte state -> Byte state -> Bool
noQisP q p = isZeroByte (mulByte q p)

||| Some Q is a P: Q · P ≠ 0.
public export
someQisP : Eq state => Byte state -> Byte state -> Bool
someQisP q p = isNonZeroByte (mulByte q p)

||| Some Q is not a P: Some active coordinate in Q is not active in P.
public export
someQnotP : Eq state => Byte state -> Byte state -> Bool
someQnotP [] _ = False
someQnotP (ZeroS :: xs) ys = someQnotP xs ys
someQnotP (OneS x w :: xs) ys =
  if w == O && lookupWeight x ys == Z
  then True
  else someQnotP xs ys
