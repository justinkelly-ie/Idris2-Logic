module Boole.Transformation

import Math.Multiset
import Math.Sing
import Boole.BF2
import Boole.BooleFraction

%default total

||| Unified state type for logic gates, combining variables and constants.
public export
data LogicState state = VarState state | ConstState TrivialBase

public export
Eq state => Eq (LogicState state) where
  (VarState x) == (VarState y) = x == y
  (ConstState BaseAnchor) == (ConstState BaseAnchor) = True
  _ == _ = False

public export
Show state => Show (LogicState state) where
  show (VarState x) = show x
  show (ConstState BaseAnchor) = "1"

||| The Transformation MSet (Logic Gate Operator):
||| A multiset of logical relations.
||| Natively mirrors the Maxel (multiset of Pixels) in spatial geometry.
public export
TransformationMSet : (state : Type) -> Type
TransformationMSet state = Multiset BF2 (SingRelation (LogicState state))

||| Transitive relation multiplication (Composition).
||| Maps [a -> b] * [c -> d] to [a -> d] iff b == c.
public export
mulRelation : Eq state => SingRelation (LogicState state) -> SingRelation (LogicState state) -> Maybe (SingRelation (LogicState state))
mulRelation (MkSingRelation a b) (MkSingRelation c d) =
  if b == c then Just (MkSingRelation a d) else Nothing

||| Relational multiset multiplication (Transitive product of multisets).
public export
mulTransformation : Eq state => TransformationMSet state -> TransformationMSet state -> TransformationMSet state
mulTransformation ZeroM _ = ZeroM
mulTransformation (AddM r1 c1 rest) m2 =
  annihilateMultiset (addMultiset (mulInner r1 c1 m2) (mulTransformation rest m2))
  where
    mulInner : SingRelation (LogicState state) -> BF2 -> TransformationMSet state -> TransformationMSet state
    mulInner _ _ ZeroM = ZeroM
    mulInner r1 c1 (AddM r2 c2 ys) =
      case mulRelation r1 r2 of
        Just rProd => insertItem rProd (mulBF2 c1 c2) (mulInner r1 c1 ys)
        Nothing    => mulInner r1 c1 ys

||| Num instance enforcing the Algebra of Boole (+ and *) over Logic Relations.
public export
Eq state => Num (TransformationMSet state) where
  (+) x y = annihilateMultiset (addMultiset x y)
  (*) = mulTransformation
  
  fromInteger 0 = ZeroM
  -- Constant one is a self-loop on the constant base anchor
  fromInteger 1 = AddM (MkSingRelation (ConstState BaseAnchor) (ConstState BaseAnchor)) O ZeroM
  fromInteger _ = ZeroM

-- =======================================================================
-- ALGEBRA OF BOOLE OPERATIONS (IN COMMENTS ONLY)
--
-- bufferGate input output = 
--   wire input output
--
-- NOT gate (bias + wire):
--   bias = MkSingRelation (ConstState BaseAnchor) (VarState output)
--   wire = MkSingRelation (VarState input) (VarState output)
--   notGate input output = bias + wire
--
-- XOR gate (wire1 + wire2):
--   xorGate in1 in2 output = wire in1 output + wire in2 output
-- =======================================================================
