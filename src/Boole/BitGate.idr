module Boole.BitGate

import Math.Multiset
import Math.BoxInt
import Boole.BF2

%default total

-----------------------------------------------------------------------
-- BIT-GATE MULTISET (Row 1 Numerator)
--
-- A type alias for a Multiset with F2 coefficients.
-- Elements are mapped to binary state flags (0 or 1).
-- Modulo-2 reduction is intrinsic: two identical elements annihilate.
--
-- NUMERATOR BOX (∈ ℤ mod 2): Active Bit Weights {b · [state]}
-----------------------------------------------------------------------

||| BIT-GATE MULTISET: A Multiset with F2 (mod-2) coefficients.
||| Addition natively performs XOR: equal states cancel (1+1=0).
public export
BitGateMset : (state : Type) -> Type
BitGateMset state = Multiset F2 state

||| The empty (zero) bit-gate state.
public export
emptyBitGate : BitGateMset state
emptyBitGate = ZeroM

||| Insert a state with a given F2 weight into the bit-gate multiset.
public export
insertBit : Eq state => state -> F2 -> BitGateMset state -> BitGateMset state
insertBit s w m = insertItem s w m

||| Evaluate the binary flag for a state by reducing the total count mod 2.
||| Traverses the multiset and XOR-accumulates the count.
public export
evaluateState : Eq state => BitGateMset state -> state -> F2
evaluateState ZeroM _ = Z
evaluateState (AddM k v rest) s =
  if k == s
    then addF2 v (evaluateState rest s)
    else evaluateState rest s

||| Lift the full multiset into BoxInt weights for transition to Row 2 (Lifted Polynombers).
||| Uses algebraic BoxInt rather than raw machine integers.
public export
liftBitGateToBoxInt : BitGateMset state -> Multiset BoxInt state
liftBitGateToBoxInt ZeroM = ZeroM
liftBitGateToBoxInt (AddM k v rest) = AddM k (f2ToBoxInt v) (liftBitGateToBoxInt rest)
