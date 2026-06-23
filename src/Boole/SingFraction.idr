module Boole.SingFraction

import Math.Multiset
import Math.Sing
import Math.Sing1
import Math.BoxInt
import Boole.BF2
import Boole.BooleFraction

%default total

||| A type alias for a Singleton Bit-Gate Multiset.
||| Instead of raw states, it wraps them in the Sing coordinate type.
public export
SingBitGateMset : (state : Type) -> Type
SingBitGateMset state = Multiset BF2 (Sing state)

||| The empty (zero) singleton bit-gate state.
public export
emptySingBitGate : SingBitGateMset state
emptySingBitGate = ZeroM

||| Insert a state with a given BF2 weight into the singleton bit-gate multiset.
public export
insertSingBit : Eq state => state -> BF2 -> SingBitGateMset state -> SingBitGateMset state
insertSingBit s w m = insertItem (MkSing s) w m

||| Evaluate the binary flag for a state in the singleton bit-gate multiset.
public export
evaluateSingState : Eq state => SingBitGateMset state -> state -> BF2
evaluateSingState ZeroM _ = Z
evaluateSingState (AddM (MkSing k) v rest) s =
  if k == s
    then addBF2 v (evaluateSingState rest s)
    else evaluateSingState rest s

||| A singleton Boole Fraction type.
||| Establishes type-level division-by-zero protection using strictly positive Sing1.
public export
record SingBooleFraction (state : Type) where
  constructor OverSingCircuit
  numeratorBitMset : SingBitGateMset state
  denominatorUnit  : Sing1 BF2 TrivialBase

||| Canonical unit denominator singleton multiset.
public export
theSingUnitConstant : Sing1 BF2 TrivialBase
theSingUnitConstant = MkSing1 (MkSing BaseAnchor) O

||| Smart constructor: builds a SingBooleFraction with the strictly positive unit denominator.
public export
mkSingBooleFraction : SingBitGateMset state -> SingBooleFraction state
mkSingBooleFraction bits = OverSingCircuit bits theSingUnitConstant

||| Evaluate a state from the singleton fraction.
public export
evalSingFraction : Eq state => SingBooleFraction state -> state -> BF2
evalSingFraction (OverSingCircuit num _) s = evaluateSingState num s

||| Lift the singleton multiset to BoxInt weights.
public export
liftSingBitGateToBoxInt : SingBitGateMset state -> Multiset BoxInt (Sing state)
liftSingBitGateToBoxInt ZeroM = ZeroM
liftSingBitGateToBoxInt (AddM k v rest) = AddM k (bf2ToBoxInt v) (liftSingBitGateToBoxInt rest)

||| Lift the singleton fraction to BoxInt, transitioning to Row 2.
public export
liftSingToRow2 : SingBooleFraction state -> Multiset BoxInt (Sing state)
liftSingToRow2 (OverSingCircuit num _) = liftSingBitGateToBoxInt num
