module Boole.BooleFraction

import Math.Multiset
import Math.BoxInt
import Boole.BF2
import Boole.BitGate

%default total

-----------------------------------------------------------------------
-- BOOLE CIRCUIT FRACTION (Row 1 Complete Type)
--
-- Encodes the full MSetFraction structure for Row 1:
--
--   NUMERATOR BOX  (∈ ℤ mod 2):  Active Bit Weights   {b · [state]}
--   DENOMINATOR BOX (∈ ℕ⁺):      Unit Constant         {1 · [Base]}
--
-- The denominator is provably the unique unit constant — no division
-- occurs. This is a dependent type constraint enforced at construction.
-----------------------------------------------------------------------

||| THE UNIT CONSTANT: The unique trivial denominator for Row 1.
||| A single base anchor element with multiplicty O (=1 in F2).
public export
data TrivialBase = BaseAnchor

public export
Eq TrivialBase where
  BaseAnchor == BaseAnchor = True

||| The canonical unit denominator multiset.
public export
theUnitConstant : BitGateMset TrivialBase
theUnitConstant = AddM BaseAnchor O ZeroM

||| Row 1 complete fraction type.
||| Pairs a BitGateMset numerator with the unit constant denominator.
||| The dependent constraint `isTrivial` verifies the denominator is exactly Unit.
public export
record BooleFraction (state : Type) where
  constructor OverCircuit
  ||| NUMERATOR: Active binary state logic flags
  numeratorBitMset : BitGateMset state
  ||| DENOMINATOR: Trivialised positive scale constant (always = 1)
  denominatorUnit  : BitGateMset TrivialBase
  ||| Dependent type proof: denominator is exactly the unit constant
  isTrivial        : denominatorUnit = BooleFraction.theUnitConstant

||| Smart constructor: builds a BooleFraction with the unit denominator.
public export
mkBooleFraction : BitGateMset state -> BooleFraction state
mkBooleFraction bits = OverCircuit bits theUnitConstant Refl

||| Evaluate a state from the fraction numerator.
public export
evalFraction : Eq state => BooleFraction state -> state -> F2
evalFraction (OverCircuit num _ _) s = evaluateState num s

||| Lift the numerator to BoxInt weights, transitioning from Row 1 → Row 2.
||| Maps F2 ∈ {Z,O} to BoxInt ∈ {0,1} for the Boole-Möbius polynomial layer.
public export
liftToRow2 : BooleFraction state -> Multiset BoxInt state
liftToRow2 (OverCircuit num _ _) = liftBitGateToBoxInt num
