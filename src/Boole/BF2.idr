module Boole.BF2

import Math.BoxInt
import Math.DepSing
import Boole.Bit

%default total

-----------------------------------------------------------------------
-- MODULO-2 LOGIC FIELD
--
-- Defined using Wildberger's recursive mset/singleton model.
-- The two elements of BF_2 ∈ {0,1} are represented as:
--   Z = Bit with weight Zero = [] = (Zero ** MkDepSing () Zero)
--   O = Bit with weight One  = [[]] = (One ** MkDepSing () One)
--
-- Uses Bit and Bit1 from Boole.Bit.
-----------------------------------------------------------------------

public export
record BF2 where
  constructor MkBF2
  content : (w : BVal ** Bit () () w)

public export
Z : BF2
Z = MkBF2 (Zero ** MkDepSing () Zero)

public export
O : BF2
O = MkBF2 (One ** MkDepSing () One)

public export
normalize : BF2 -> BF2
normalize (MkBF2 (Zero ** _)) = Z
normalize (MkBF2 (One  ** _)) = O

public export
Eq BF2 where
  (MkBF2 (w1 ** _)) == (MkBF2 (w2 ** _)) = w1 == w2

public export
Show BF2 where
  show x = if x == Z then "0" else "1"

||| BOOLEAN RING EVALUATION: XOR Addition (1 + 1 = 0)
public export
addBF2 : BF2 -> BF2 -> BF2
addBF2 (MkBF2 (w1 ** b1)) (MkBF2 (w2 ** b2)) =
  let sumBit = addBit b1 b2
  in MkBF2 ((w1 + w2) ** sumBit)

||| AND Multiplication (1 * 1 = 1)
public export
mulBF2 : BF2 -> BF2 -> BF2
mulBF2 (MkBF2 (w1 ** b1)) (MkBF2 (w2 ** b2)) =
  let prodWeight = w1 * w2
  in MkBF2 (prodWeight ** MkDepSing () prodWeight)

public export
Num BF2 where
  (+) = addBF2
  (*) = mulBF2
  fromInteger 0 = Z
  fromInteger 1 = O
  fromInteger n = if mod n 2 == 0 then Z else O

||| Lift a BF2 element to a natural number (0 or 1)
public export
bf2ToNat : BF2 -> Nat
bf2ToNat x = if x == Z then 0 else 1

||| Lift a BF2 element to a BoxInt weight for Row 2 transition.
||| Maps the bi-field {Z,O} into algebraic integer space without raw casting.
public export
bf2ToBoxInt : BF2 -> BoxInt
bf2ToBoxInt x = if x == Z then intToBoxInt 0 else intToBoxInt 1
