module Boole.BF2

import Math.BoxInt

%default total

-----------------------------------------------------------------------
-- MODULO-2 LOGIC FIELD
--
-- The two elements of F_2 ∈ {0,1} as a strict modulo-2 type.
-- This is the coefficient field for the Boolean Ring (Row 1).
-- Addition is XOR (1 + 1 = 0); multiplication is AND (1 * 1 = 1).
-----------------------------------------------------------------------

public export
data F2 = Z | O

public export
Eq F2 where
  Z == Z = True
  O == O = True
  _ == _ = False

public export
Show F2 where
  show Z = "0"
  show O = "1"

||| BOOLEAN RING EVALUATION: XOR Addition (1 + 1 = 0)
public export
addF2 : F2 -> F2 -> F2
addF2 Z x = x
addF2 x Z = x
addF2 O O = Z

||| AND Multiplication (1 * 1 = 1)
public export
mulF2 : F2 -> F2 -> F2
mulF2 O O = O
mulF2 _ _ = Z

public export
Num F2 where
  (+) = addF2
  (*) = mulF2
  fromInteger 0 = Z
  fromInteger 1 = O
  fromInteger _ = Z

||| Lift an F2 element to a natural number (0 or 1)
public export
f2ToNat : F2 -> Nat
f2ToNat Z = 0
f2ToNat O = 1

||| Lift an F2 element to a BoxInt weight for Row 2 transition.
||| Maps the bi-field {Z,O} into algebraic integer space without raw casting.
public export
f2ToBoxInt : F2 -> BoxInt
f2ToBoxInt Z = intToBoxInt 0
f2ToBoxInt O = intToBoxInt 1
