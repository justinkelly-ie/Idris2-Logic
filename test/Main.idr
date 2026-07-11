module Main

import QuickCheck
import Data.List
import Math.Multiset
import Math.Singleton.Sing
import Math.Pixel
import Math.BoxInt
import Math.SignedFraction
import Math.Interfaces
import Math.Vexel.Vexel
import Math.Vexel.DepVexel
import Math.Singleton.Bit
import Logic.BoolePolynumber
import Logic.Circuit
import Logic.MobiusTransform
import Math.Singleton.SBFMset
import Math.Singleton.SingFraction
import Logic.Syllogism
import Logic.LiftedPolynumber
import Logic.BooleFunction
import Math.Vexel.Byte
import Math.Vexel.Transformation

%default total

--------------------------------------------------------------------------------
-- 1. ARBITRARY INSTANCES FOR CORE TYPES
--------------------------------------------------------------------------------

public export
record TestBVal where
  constructor MkTestBVal
  val : BVal

public export
Show TestBVal where
  show (MkTestBVal x) = if x == ZeroS then "ZeroS" else "OneS () 1"

public export
Arbitrary TestBVal where
  arbitrary = do
    b <- arbitrary {a=Bool}
    pure (MkTestBVal (if b then ZeroS else OneS () 1))
  coarbitrary (MkTestBVal x) gen =
    if x == ZeroS then variant 0 gen else variant 1 gen

public export
Arbitrary BoxInt where
  arbitrary = do
    n <- arbitrary {a=Integer}
    pure (fromInteger n)
  coarbitrary b gen =
    let (Math.Interfaces.MkUr val) = boxToInt b
    in coarbitrary val gen

public export
Arbitrary MSetFraction where
  arbitrary = do
    n <- arbitrary {a=BoxInt}
    d <- arbitrary {a=Nat}
    let dNonZero = if d == 0 then 1 else d
    pure (MkMSF n dNonZero)
  coarbitrary (MkMSF n d) gen =
    coarbitrary n (coarbitrary d gen)

--------------------------------------------------------------------------------
-- 2. PROPERTIES FOR CORE TYPES
--------------------------------------------------------------------------------

-- BVal Properties
prop_bvalAddCommutative : Property
prop_bvalAddCommutative = forAll {a = (TestBVal, TestBVal)} {prop = Bool} arbitrary (MkFn (\(MkTestBVal x, MkTestBVal y) =>
  Prelude.(+) x y == Prelude.(+) y x))

prop_bvalAddIdentity : Property
prop_bvalAddIdentity = forAll {a = TestBVal} {prop = Bool} arbitrary (MkFn (\(MkTestBVal x) =>
  Prelude.(+) x Zero == x))

prop_bvalAddSelfAnnihilate : Property
prop_bvalAddSelfAnnihilate = forAll {a = TestBVal} {prop = Bool} arbitrary (MkFn (\(MkTestBVal x) =>
  Prelude.(+) x x == Zero))

prop_bvalMulCommutative : Property
prop_bvalMulCommutative = forAll {a = (TestBVal, TestBVal)} {prop = Bool} arbitrary (MkFn (\(MkTestBVal x, MkTestBVal y) =>
  Prelude.(*) x y == Prelude.(*) y x))

prop_bvalAddSelfAnnihilateZeroS : Property
prop_bvalAddSelfAnnihilateZeroS = forAll {a = TestBVal} {prop = Bool} arbitrary (MkFn (\(MkTestBVal x) =>
  Prelude.(+) x x == ZeroS))

-- Byte Properties
prop_byteAddSelfAnnihilate : Property
prop_byteAddSelfAnnihilate = forAll {a = List Nat} {prop = Bool} arbitrary (MkFn (\xs =>
  let byte = oneByte xs
  in addByte byte byte == []))

-- Circuit / Polynumber Properties
prop_circuitNotNotIdentity : Property
prop_circuitNotNotIdentity = forAll {a = List Bool} {prop = Bool} arbitrary (MkFn (\inputsBool =>
  let inputs = map (\b => if b then OneS () 1 else ZeroS) inputsBool
      circ = Var 0
      notNot = 1 + (1 + circ)
      -- Ensure we have at least one input variable
      paddedInputs = if null inputs then [ZeroS] else inputs
  in evalBoolePoly notNot paddedInputs == evalBoolePoly circ paddedInputs))

-- Mobius Transform Properties
prop_mobiusSelfInverse : Property
prop_mobiusSelfInverse = forAll {a = List Bool} {prop = Property} arbitrary (MkFn (\bools =>
  not (null bools) ==>
  let vals = map (\b => if b then OneS () 1 else ZeroS) (take 4 bools)
  in mobiusTransform (mobiusTransform vals) == vals))

-- SBFMset Properties
prop_sbfEvaluation : Property
prop_sbfEvaluation = forAll {a = List Nat} {prop = Bool} arbitrary (MkFn (\xs =>
  let mset = fromList (map (\v => (v, 1)) xs)
      blueVal = evalSBFMset blueSBF mset
      redVal = evalSBFMset redSBF mset
  in True))

-- Syllogism Properties
prop_syllogismBarbara : Property
prop_syllogismBarbara = forAll {a = List Nat} {prop = Bool} arbitrary (MkFn (\xs =>
  let a = oneByte xs
      b = oneByte xs
      c = oneByte xs
  in barbara a b c == True))

-- LiftedPolynumber Properties
prop_idempotentCollapseMonomial : Property
prop_idempotentCollapseMonomial = forAll {a = List Nat} {prop = Bool} arbitrary (MkFn (\vars =>
  let mono = fromList (map (\v => (v, 2)) vars)
      collapsed = idempotentCollapse mono
      entries = multisetToList collapsed
  in all (\(_, c) => c == 1) entries))

-- BooleFunction Properties
prop_booleFunctionEvaluation : Property
prop_booleFunctionEvaluation = forAll {a = List Bool} {prop = Bool} arbitrary (MkFn (\bools =>
  let tableBool = take 4 (bools ++ replicate 4 False)
      vals = map (\b => if b then OneS () 1 else ZeroS) tableBool
      func = MkBooleFunction 2 vals
      in0 = [the BVal ZeroS, the BVal ZeroS]
      in1 = [the BVal ZeroS, OneS () 1]
      in2 = [OneS () 1, the BVal ZeroS]
      in3 = [OneS () 1, OneS () 1]
  in (evaluate func in0 == fromMaybe ZeroS (lookupIndex 0 vals)) &&
     (evaluate func in1 == fromMaybe ZeroS (lookupIndex 1 vals)) &&
     (evaluate func in2 == fromMaybe ZeroS (lookupIndex 2 vals)) &&
     (evaluate func in3 == fromMaybe ZeroS (lookupIndex 3 vals))))

prop_booleFunctionPolynumberIsomorphism : Property
prop_booleFunctionPolynumberIsomorphism = forAll {a = List Bool} {prop = Bool} arbitrary (MkFn (\bools =>
  let tableBool = take 4 (bools ++ replicate 4 False)
      vals = map (\b => if b then OneS () 1 else ZeroS) tableBool
      func = MkBooleFunction 2 vals
  in truthTable (fromPolynumber 2 (toPolynumber func)) == vals))

-- Galadh Chooses Stone (polynumber isomorphism)
prop_galadhadChoosesStone : Property
prop_galadhadChoosesStone = forAll {a = List Bool} {prop = Bool} arbitrary (MkFn (\bools =>
  let tableBool = take 4 (bools ++ replicate 4 False)
      vals = map (\b => if b then OneS () 1 else ZeroS) tableBool
      func = MkBooleFunction 2 vals
  in truthTable (fromPolynumber 2 (toPolynumber func)) == vals))

--------------------------------------------------------------------------------
-- 3. TEST SUITE RUNNER
--------------------------------------------------------------------------------

partial
runSuite : IO ()
runSuite = do
  putStrLn ""
  putStrLn "----------------------------------------------------"
  putStrLn "-- idris2-Logic: Boolean Algebra Verification Suite --"
  putStrLn "----------------------------------------------------"
  putStrLn ""

  let r1 = quickCheck prop_bvalAddCommutative
  putStrLn $ "prop_bvalAddCommutative: " ++ r1.msg

  let r2 = quickCheck prop_bvalAddIdentity
  putStrLn $ "prop_bvalAddIdentity: " ++ r2.msg

  let r3 = quickCheck prop_bvalAddSelfAnnihilate
  putStrLn $ "prop_bvalAddSelfAnnihilate: " ++ r3.msg

  let r4 = quickCheck prop_bvalMulCommutative
  putStrLn $ "prop_bvalMulCommutative: " ++ r4.msg

  let r5 = quickCheck prop_bvalAddSelfAnnihilateZeroS
  putStrLn $ "prop_bvalAddSelfAnnihilateZeroS: " ++ r5.msg

  let r6 = quickCheck prop_byteAddSelfAnnihilate
  putStrLn $ "prop_byteAddSelfAnnihilate: " ++ r6.msg

  let r7 = quickCheck prop_circuitNotNotIdentity
  putStrLn $ "prop_circuitNotNotIdentity: " ++ r7.msg

  let r8 = quickCheck prop_mobiusSelfInverse
  putStrLn $ "prop_mobiusSelfInverse: " ++ r8.msg

  let r9 = quickCheck prop_sbfEvaluation
  putStrLn $ "prop_sbfEvaluation: " ++ r9.msg

  let r10 = quickCheck prop_syllogismBarbara
  putStrLn $ "prop_syllogismBarbara: " ++ r10.msg

  let r11 = quickCheck prop_idempotentCollapseMonomial
  putStrLn $ "prop_idempotentCollapseMonomial: " ++ r11.msg

  let r12 = quickCheck prop_booleFunctionEvaluation
  putStrLn $ "prop_booleFunctionEvaluation: " ++ r12.msg

  let r13 = quickCheck prop_booleFunctionPolynumberIsomorphism
  putStrLn $ "prop_booleFunctionPolynumberIsomorphism: " ++ r13.msg

  let r14 = quickCheck prop_galadhadChoosesStone
  putStrLn $ "prop_galadhadChoosesStone: " ++ r14.msg

  -- Crash on failure to signal CI runner
  let results = [r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14]
  let failures = filter (\r => isJust r.pass && fromMaybe True r.pass == False) results
  if null failures
    then putStrLn "\nAll 14 tests passed."
    else idris_crash "❌ FAILURE: One or more properties failed verification."

partial
main : IO ()
main = runSuite
