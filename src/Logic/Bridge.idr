module Logic.Bridge

import Math.Multiset
import Math.BoxInt
import Math.IntPolynumber
import Math.SignedFraction
import Math.Singleton.Sing
import Math.Singleton.Bit
import Logic.BoolePolynumber
import Logic.MobiusTransform

%default covering

-----------------------------------------------------------------------
-- BOOLE → BOXINT BRIDGE
--
-- Row 1 (Digital Repetition) operates over Bit ∈ {0,1} (𝔽₂).
-- Row 2 (Lifted Polynumbers) operates over BoxInt ∈ ℤ.
--
-- This module provides the embedding and the integer-valued
-- Boole-Möbius transform that connects the two layers.
--
-- Source: Wildberger Lectures 270–272.
-----------------------------------------------------------------------

||| Embed a Bit list (truth table or coefficient vector) into BoxInt list.
public export
bitsToBoxInts : List Bit -> List BoxInt
bitsToBoxInts = map bitToBoxInt

-----------------------------------------------------------------------
-- 2. LIFTING: BoolePolynumber → IntPolynumber
-----------------------------------------------------------------------

||| Lift a BoolePolynumber (Multiset BVal Nat) to IntPolynumber (Multiset BoxInt (Nat, Nat)).
||| The subset index k maps to power pair (k, 0) — beta is always 0 for
||| pure logical polynomials (no secondary variable axis).
public export
booleToIntPoly : BoolePolynumber -> IntPolynumber
booleToIntPoly ZeroM = ZeroM
booleToIntPoly (AddM subsetIdx coeff rest) =
  let boxCoeff = bitToBoxInt coeff
  in if boxCoeff == 0
     then booleToIntPoly rest
     else AddM (subsetIdx, 0) boxCoeff (booleToIntPoly rest)

-----------------------------------------------------------------------
-- 3. INTEGER-VALUED BOOLE-MÖBIUS TRANSFORM
--
-- The transform T(i,j) = 1 iff i ⊆ j (subset inclusion).
-- Over ℤ (not 𝔽₂), T is NOT self-inverse.  The inverse uses
-- Möbius inversion with alternating signs (inclusion-exclusion).
--
-- Forward:  y_I = Σ_{J ⊇ I} x_J
-- Inverse:  x_I = Σ_{J ⊇ I} (-1)^{|J\I|} · y_J
-----------------------------------------------------------------------

||| Count the number of set bits in a Nat (population count).
public export
popCount : Nat -> Nat
popCount Z = Z
popCount n =
  let low = if isOdd n then 1 else 0
  in low + popCount (assert_smaller n (half n))

||| Check if a Nat is even via structural recursion.
public export
evenNat : Nat -> Bool
evenNat Z = True
evenNat (S Z) = False
evenNat (S (S k)) = evenNat k

||| Forward integer Boole-Möbius transform.
||| T_n · x: accumulates subset weights into supersets.
public export
mobiusTransformZ : List BoxInt -> List BoxInt
mobiusTransformZ xs =
  let size = length xs
  in map (\i => foldRowZ i 0 xs) [0 .. minus size 1]
  where
    foldRowZ : Nat -> Nat -> List BoxInt -> BoxInt
    foldRowZ _ _ [] = 0
    foldRowZ i j (x :: rest) =
      let contrib = if isSubsetNat i j then x else 0
      in contrib + foldRowZ i (S j) rest

||| Inverse integer Boole-Möbius transform (Möbius inversion).
||| T_n⁻¹ · y: recovers individual weights via inclusion-exclusion.
||| x_i = Σ_{j ⊇ i} (-1)^{|j \ i|} · y_j
public export
mobiusInverseZ : List BoxInt -> List BoxInt
mobiusInverseZ ys =
  let size = length ys
  in map (\i => foldInvRowZ i 0 ys) [0 .. minus size 1]
  where
    ||| Lookup the j-th element of a list, returning 0 if out of bounds.
    lookupZ : Nat -> List BoxInt -> BoxInt
    lookupZ _ [] = 0
    lookupZ Z (x :: _) = x
    lookupZ (S k) (_ :: rest) = lookupZ k rest

    foldInvRowZ : Nat -> Nat -> List BoxInt -> BoxInt
    foldInvRowZ _ _ [] = 0
    foldInvRowZ i j (y :: rest) =
      if isSubsetNat i j
      then let diffBits = popCount j `minus` popCount i
               sign = if evenNat diffBits then 1 else (-1)
           in (sign * y) + foldInvRowZ i (S j) rest
      else foldInvRowZ i (S j) rest

-----------------------------------------------------------------------
-- 4. BOOLEAN FUNCTION → INTEGER POLYNOMIAL (Full Pipeline)
-----------------------------------------------------------------------

||| Full pipeline: truth table (Bit) → Möbius lift → integer polynomial.
||| Applies the Bit Möbius transform first, then embeds the result
||| as an IntPolynumber.
public export
truthTableToIntPoly : List Bit -> IntPolynumber
truthTableToIntPoly tt =
  let boole = boolFuncToBoole tt
  in booleToIntPoly boole

||| Full pipeline: truth table (Bit) → integer Möbius transform.
||| Embeds Bit → BoxInt first, then applies the ℤ-valued transform.
public export
truthTableToBoxInts : List Bit -> List BoxInt
truthTableToBoxInts tt = mobiusTransformZ (bitsToBoxInts tt)

-----------------------------------------------------------------------
-- 5. LINEAR BRIDGE FRACTION INTEGRATION
-----------------------------------------------------------------------

||| Wrap an IntPolynumber coefficient as an MSetFraction (n/1).
||| Every Boole polynomial coefficient is an integer with unit denominator.
public export
coeffToMSF : BoxInt -> MSetFraction
coeffToMSF = fromBoxInt
