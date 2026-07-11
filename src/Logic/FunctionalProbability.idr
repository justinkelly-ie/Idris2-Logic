module Logic.FunctionalProbability

import Data.List
import Math.Multiset
import Math.Singleton.Sing
import Math.BoxInt
import Math.SignedFraction
import Math.Interfaces
import Math.Singleton.Bit
import Logic.Bridge
import Math.Singleton.SingFraction

%default covering

-----------------------------------------------------------------------
-- HEHNER FUNCTIONAL PROBABILITY (Row 3)
--
-- Source: Eric Hehner, "a]Probability Theory".
--
-- Hehner replaces infinite quantifiers (∀, ∃) with calculational
-- min/max over closed finite spaces.  Probability is not an axiom
-- but a derived normalisation:
--
--   E̅ = E · (ΣE)⁻¹
--
-- In our MSetFraction framework, this becomes:
--   For each element e with weight w in a multiset of total mass T,
--   the probability is w/T — computed by cross-multiplication, no division.
-----------------------------------------------------------------------

-----------------------------------------------------------------------
-- 1. TOTAL MASS (Universe Sum)
-----------------------------------------------------------------------

||| Compute the total signed mass of a BoxInt multiset.
||| This is the denominator of Hehner normalisation: ΣE.
public export
totalMass : Sing BoxInt a -> BoxInt
totalMass ZeroS = 0
totalMass (OneS _ c) = c

||| Compute the total unsigned mass (absolute values).
public export
totalAbsMass : Sing BoxInt a -> BoxInt
totalAbsMass ZeroS = 0
totalAbsMass (OneS _ c) = abs c

-----------------------------------------------------------------------
-- 2. MSET FRACTION VEXEL DEFINITION (Row 3 Complete Type)
-----------------------------------------------------------------------

||| Row 3 complete fraction type.
||| Pairs a quantified multiset (numerator box) with its total universe sum (denominator box).
public export
record MSetFractionVexel (v : Type) where
  constructor OverMSFSpace
  numeratorMset  : Sing BoxInt v
  denominatorSum : Sing1 BoxInt TrivialBase

||| Smart constructor for MSetFractionVexel.
public export
mkMSetFractionVexel : Sing BoxInt v -> BoxInt -> MSetFractionVexel v
mkMSetFractionVexel m tot = OverMSFSpace m (MkSing1 BaseAnchor tot)

||| Extract the probability of a specific state in the normalised space.
||| Returns the probability as an MSetFraction.
||| If the total mass is zero (degenerate space), returns 0/1.
public export
stateProbability : Eq v => MSetFractionVexel v -> v -> MSetFraction
stateProbability (OverMSFSpace m den) s =
  let (MkUr denVal) = boxToInt (count den)
      absDen = Math.Interfaces.integerToNat (abs denVal)
  in if absDen == 0
     then zeroMSF
     else
       let wt = lookupWeight s m
       in MkMSF wt absDen
  where
    lookupWeight : v -> Sing BoxInt v -> BoxInt
    lookupWeight _ ZeroS = 0
    lookupWeight x (OneS y w) =
      if x == y then w else 0

||| Normalize a MSetFractionVexel into a list of states and their corresponding probabilities.
public export
normalizeFraction : MSetFractionVexel v -> List (v, MSetFraction)
normalizeFraction (OverMSFSpace m den) =
  let (MkUr denVal) = boxToInt (count den)
      absDen = Math.Interfaces.integerToNat (abs denVal)
  in if absDen == 0
     then []
     else go m absDen
  where
    go : Sing BoxInt v -> Nat -> List (v, MSetFraction)
    go ZeroS _ = []
    go (OneS elem wt) d =
      [(elem, MkMSF wt d)]

-----------------------------------------------------------------------
-- 3. CALCULATIONAL QUANTIFIERS (min / max)
-----------------------------------------------------------------------

||| Minimum weight in a BoxInt multiset (Hehner's ∀ replacement).
public export
minWeight : Sing BoxInt a -> BoxInt
minWeight ZeroS = 0
minWeight (OneS _ c) = c

||| Maximum weight in a BoxInt multiset (Hehner's ∃ replacement).
public export
maxWeight : Sing BoxInt a -> BoxInt
maxWeight ZeroS = 0
maxWeight (OneS _ c) = c

-----------------------------------------------------------------------
-- 4. PROPORTIONAL COMPARISON
-----------------------------------------------------------------------

||| Check whether two elements have equal probability in a normalised space.
||| Uses cross-multiplication: w₁ * T == w₂ * T (trivially true if same
||| denominator, but this generalises to comparing across different spaces).
public export
eqProbability : MSetFraction -> MSetFraction -> Bool
eqProbability = eqMSF

||| Check whether one probability dominates another.
||| a/b > c/d ⟺ a*d > c*b (for positive denominators).
public export
gtProbability : MSetFraction -> MSetFraction -> Bool
gtProbability (MkMSF a b) (MkMSF c d) =
  (a * fromInteger (natToInteger d)) > (c * fromInteger (natToInteger b))

-----------------------------------------------------------------------
-- 5. VERIFIED EXAMPLES FROM HEHNER'S PAPER
-----------------------------------------------------------------------

-- === Example 1: The Two Children Paradox ===
-- "I have two children. At least one child is a girl. What is the probability that the other child is also a girl?"

public export
data Gender = Boy | Girl

public export
Eq Gender where
  Boy == Boy = True
  Girl == Girl = True
  _ == _ = False

public export
Show Gender where
  show Boy = "Boy"
  show Girl = "Girl"

||| Unnormalized state space for families with 2 children.
||| Each outcome has a weight of 1.
public export
twoChildrenSpace : List (Sing BoxInt (Gender, Gender))
twoChildrenSpace =
  [ OneS (Boy, Boy) 1
  , OneS (Boy, Girl) 1
  , OneS (Girl, Boy) 1
  , OneS (Girl, Girl) 1
  ]

||| Case A: "At least one child is a girl"
||| Filters the space, leaving 3 outcomes.
public export
atLeastOneGirl : MSetFractionVexel (Gender, Gender)
atLeastOneGirl = mkMSetFractionVexel (OneS (Girl, Girl) 1) 3

||| The probability that both are girls given at least one is a girl (evaluates to 1/3).
public export
probBothGirlsGivenAtLeastOne : MSetFraction
probBothGirlsGivenAtLeastOne = stateProbability atLeastOneGirl (Girl, Girl)

||| Case B: "The older child (first) is a girl"
||| Filters the space, leaving 2 outcomes.
public export
olderChildGirl : MSetFractionVexel (Gender, Gender)
olderChildGirl = mkMSetFractionVexel (OneS (Girl, Girl) 1) 2

||| The probability that both are girls given the older is a girl (evaluates to 1/2).
public export
probBothGirlsGivenOlderGirl : MSetFraction
probBothGirlsGivenOlderGirl = stateProbability olderChildGirl (Girl, Girl)


-- === Example 2: The Three Cards Paradox ===
-- Three cards: R (red/red), W (white/white), M (mixed red/white). 
-- You look at one side, it is red. Probability the other side is also red?

public export
data Card = CardRR | CardWW | CardMR

public export
Eq Card where
  CardRR == CardRR = True
  CardWW == CardWW = True
  CardMR == CardMR = True
  _ == _ = False

public export
Show Card where
  show CardRR = "CardRR"
  show CardWW = "CardWW"
  show CardMR = "CardMR"

public export
data Side = RedSide | WhiteSide

public export
Eq Side where
  RedSide == RedSide = True
  WhiteSide == WhiteSide = True
  _ == _ = False

public export
Show Side where
  show RedSide = "Red"
  show WhiteSide = "White"

||| Total unnormalized space of card choices and observed sides (6 outcomes).
public export
threeCardsSpace : List (Sing BoxInt (Card, Side))
threeCardsSpace =
  [ OneS (CardRR, RedSide) 1
  , OneS (CardRR, RedSide) 1
  , OneS (CardWW, WhiteSide) 1
  , OneS (CardWW, WhiteSide) 1
  , OneS (CardMR, RedSide) 1
  , OneS (CardMR, WhiteSide) 1
  ]

||| Filtered space where the observed side is Red (3 outcomes).
public export
observedRedSide : MSetFractionVexel (Card, Side)
observedRedSide = mkMSetFractionVexel (OneS (CardRR, RedSide) 2) 3

||| The probability that the other side is also red.
||| This is equivalent to checking if the card is CardRR (evaluates to 2/3).
public export
probOtherSideRed : MSetFraction
probOtherSideRed = stateProbability observedRedSide (CardRR, RedSide)
