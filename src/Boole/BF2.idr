module Boole.BF2

import Math.Sing
import Math.BoxInt
import public Boole.Bit

%default total

-----------------------------------------------------------------------
-- MODULO-2 LOGIC FIELD OVER SINGLETONS
--
-- Alias to BVal, fully utilizing the singleton multiset representation.
-----------------------------------------------------------------------

public export
BF2 : Type
BF2 = BVal

public export
Z : BF2
Z = Zero

public export
O : BF2
O = One

public export
normalize : BF2 -> BF2
normalize x = if x == Zero then Z else O

public export
addBF2 : BF2 -> BF2 -> BF2
addBF2 = addBVal

public export
mulBF2 : BF2 -> BF2 -> BF2
mulBF2 = mulBVal

public export
bf2ToNat : BF2 -> Nat
bf2ToNat = bvalToNat

public export
bf2ToBoxInt : BF2 -> BoxInt
bf2ToBoxInt x = if x == Z then intToBoxInt 0 else intToBoxInt 1
