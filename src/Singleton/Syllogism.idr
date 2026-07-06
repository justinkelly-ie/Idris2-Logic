module Singleton.Syllogism

import Data.Vect
import Singleton.Bit
import Vexel.Byte

%default total

-----------------------------------------------------------------------
-- ARISTOTELIAN SYLLOGISMS VIA THE ALGEBRA OF BOOLE
--
-- Source: Wildberger Lectures 255–257, 275, 280.
-----------------------------------------------------------------------

public export
0 Predication : Type
Predication = Nat

public export
EveryQisP  : Predication
EveryQisP  = 0

public export
NoQisP     : Predication
NoQisP     = 1

public export
SomeQisP   : Predication
SomeQisP   = 2

public export
SomeQnotP  : Predication
SomeQnotP  = 3

public export
showPredication : Predication -> String
showPredication 0 = "Every Q is a P"
showPredication 1 = "No Q is a P"
showPredication 2 = "Some Q is a P"
showPredication 3 = "Some Q is not a P"
showPredication _ = "Unknown predication"

public export
checkPredication : Eq state => Predication -> Byte state -> Byte state -> Bool
checkPredication 0  q p = everyQisP q p
checkPredication 1  q p = noQisP q p
checkPredication 2  q p = someQisP q p
checkPredication 3  q p = someQnotP q p
checkPredication _  _ _ = False

-----------------------------------------------------------------------
-- FIRST FIGURE
-----------------------------------------------------------------------

||| Barbara: Every B is A, Every C is B ⊢ Every C is A.
public export
barbara : Eq state => (a, b, c : Byte state) -> Bool
barbara a b c =
  if everyQisP b a && everyQisP c b
  then everyQisP c a
  else True

||| Celarent: No B is A, Every C is B ⊢ No C is A.
public export
celarent : Eq state => (a, b, c : Byte state) -> Bool
celarent a b c =
  if noQisP b a && everyQisP c b
  then noQisP c a
  else True

||| Darii: Every B is A, Some C is B ⊢ Some C is A.
public export
darii : Eq state => (a, b, c : Byte state) -> Bool
darii a b c =
  if everyQisP b a && someQisP c b
  then someQisP c a
  else True

||| Ferio: No B is A, Some C is B ⊢ Some C is not A.
public export
ferio : Eq state => (a, b, c : Byte state) -> Bool
ferio a b c =
  if noQisP b a && someQisP c b
  then someQnotP c a
  else True

-----------------------------------------------------------------------
-- SECOND FIGURE
-----------------------------------------------------------------------

public export
cesare : Eq state => (p, m, s : Byte state) -> Bool
cesare p m s =
  if noQisP p m && everyQisP s m
  then noQisP s p
  else True

public export
camestres : Eq state => (p, m, s : Byte state) -> Bool
camestres p m s =
  if everyQisP p m && noQisP s m
  then noQisP s p
  else True

-----------------------------------------------------------------------
-- STOIC LOGIC
-----------------------------------------------------------------------

||| Modus Ponens: P, P→Q ⊢ Q.
||| P→Q = 1 + P + PQ. Premise P·(1+P+PQ) = PQ.
public export
modusPonens : BVal -> BVal -> BVal
modusPonens p q =
  let premise = p * (One + p + p * q)
  in if premise == Zero
     then One
     else q

||| Modus Tollens: P→Q, ¬Q ⊢ ¬P.
public export
modusTollens : BVal -> BVal -> BVal
modusTollens p q =
  let implication = One + p + p * q
      notQ = One + q
      premise = implication * notQ
      notP = One + p
  in if premise == Zero
     then One
     else notP

-----------------------------------------------------------------------
-- GENERIC VERIFICATION
-----------------------------------------------------------------------

public export
verifySyllogism : Eq state
              => (Predication, Byte state, Byte state)
              -> (Predication, Byte state, Byte state)
              -> (Predication, Byte state, Byte state)
              -> Bool
verifySyllogism (pred1, q1, p1) (pred2, q2, p2) (conc, qc, pc) =
  if checkPredication pred1 q1 p1 && checkPredication pred2 q2 p2
  then checkPredication conc qc pc
  else True
