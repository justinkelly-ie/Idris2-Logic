module Boole.SingFraction

import Math.Multiset
import Math.Sing
import Math.Sing1
import Math.BoxInt
import Boole.BF2
import Boole.BooleFraction

%default total

||| A type alias for a Singleton Bit-Gate Multiset.
||| Defined directly as the Sing multiset with weights BF2.
public export
SingBitGateMset : (state : Type) -> Type
SingBitGateMset state = Sing BF2 state

||| The empty (zero) singleton bit-gate state.
public export
emptySingBitGate : SingBitGateMset state
emptySingBitGate = ZeroS

||| Insert a state with a given BF2 weight into the singleton bit-gate multiset.
public export
insertSingBit : Eq state => state -> BF2 -> SingBitGateMset state -> SingBitGateMset state
insertSingBit s w m =
  if w == Z then m else OneS s w

||| Evaluate the binary flag for a state in the singleton bit-gate multiset.
public export
evaluateSingState : Eq state => SingBitGateMset state -> state -> BF2
evaluateSingState ZeroS _ = Z
evaluateSingState (OneS k v) s =
  if k == s
    then v
    else Z

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
theSingUnitConstant = MkSing1 BaseAnchor O

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
liftSingBitGateToBoxInt : SingBitGateMset state -> Sing BoxInt state
liftSingBitGateToBoxInt ZeroS = ZeroS
liftSingBitGateToBoxInt (OneS k v) = OneS k (bf2ToBoxInt v)

||| Lift the singleton fraction to BoxInt, transitioning to Row 2.
public export
liftSingToRow2 : SingBooleFraction state -> Sing BoxInt state
liftSingToRow2 (OverSingCircuit num _) = liftSingBitGateToBoxInt num
