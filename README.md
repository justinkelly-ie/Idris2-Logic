# 🎛️ idris2-Boole

**A formalization of Norman Wildberger's *Algebra of Boole* in [Idris 2](https://github.com/idris-lang/Idris2).**

[![Idris2](https://img.shields.io/badge/Idris2-Algebra-blue.svg)](https://github.com/idris-lang/Idris2)

---

## 🏛️ The Algebraic Nature of the Algebra of Boole

Wildberger's **Algebra of Boole** (originating from George Boole's original 1847 work *The Mathematical Analysis of Logic*) is a system of **mod-2 arithmetic**, not symbolic logic. It differs fundamentally from Huntington and Shannon's modern *Boolean Algebra* by treating exclusive-or (XOR) as the primitive addition operator.

### The Fundamental Shift: Self-Annihilation and Inverse

In standard Boolean algebra, addition is inclusive OR ($\lor$). Because $1 \lor 1 = 1$, the elements lack an additive inverse. You cannot subtract, and standard tools of linear algebra are unusable.

In the Algebra of Boole, addition is modulo-2 XOR ($+$). Because **$x + x = 0$**, every element is its own additive inverse. This simple property turns the system into a **Boolean Ring** (a commutative ring with identity where every element is idempotent, $x^2 = x$):

| Property | Algebra of Boole ($B_2$ Commutative Ring) | Boolean Algebra (Distributive Lattice) |
|---|---|---|
| **Addition ($+$)** | `+` (XOR / Exclusive OR) | `∨` (OR / Inclusive OR) |
| **Multiplication ($\cdot$)** | `*` (AND) | `∧` (AND) |
| **Annihilation** | $1 + 1 = 0$ | $1 \lor 1 = 1$ |
| **Additive Inverse** | Yes (each element is its own inverse: $x + x = 0$) | No |
| **Subtraction** | Fully supported ($x - y \equiv x + y$) | Not defined |
| **Complement (NOT $x$)** | $1 + x$ (algebraically derived) | $\bar{x}$ (primitive connective) |
| **Inclusive OR ($x \lor y$)** | $x + y + xy$ (algebraically derived) | $x \lor y$ (primitive connective) |
| **Representation** | **Unique** multilinear polynomial (Boole polynumber) | Non-unique sum-of-products |
| **Equivalence** | Direct coefficient vector comparison | SAT problem (NP-complete) |

---

## 🗃️ Core Algebraic Architecture

This library implements the Algebra of Boole as the foundational layer (**Row 1**) of the **Global Finite Science Table**. All elements are modeled as fractional structures of multisets to enable smooth functorial transitions to higher physics and probability layers:

$$\text{BooleFraction} = \frac{\text{Numerator Box} \;\in \mathbb{F}_2}{\text{Denominator Box} \;\in \mathbb{F}_2} \quad \text{where} \quad \text{Denominator} = \{1 \cdot [\text{Base}]\}$$

### The Three Core Types

#### 1. `F2` — Wildberger's Bi-Field ([BF2.idr](file:///var/home/justin/Projects/Idris2-Boole/src/Boole/BF2.idr))
The coefficient field $B_2 = \{0, 1\}$. It is implemented as a strict, non-castable algebraic type `data F2 = Z | O` with a `Num` instance defining addition mod 2 ($O + O = Z$) and multiplication ($O * O = O$).

#### 2. `BitGateMset` — The Numerator Box ([BitGate.idr](file:///var/home/justin/Projects/Idris2-Boole/src/Boole/BitGate.idr))
A multiset over a state type with `F2` coefficients. Because coefficients are in $F_2$, state addition automatically simplifies via XOR: inserting duplicate states cancels them out ($s + s = 0$). This acts as a coordinate vector representing a circuit's active states.

#### 3. `BooleFraction` — The Complete Row 1 Type ([BooleFraction.idr](file:///var/home/justin/Projects/Idris2-Boole/src/Boole/BooleFraction.idr))
A fractional container `BooleFraction state` holding:
- `numeratorBitMset`: The active circuit multiset weights.
- `denominatorUnit`: The unit scale multiset.
- `isTrivial`: A **dependent type proof** verifying at compile-time that the denominator is exactly the unit constant $1$. This anchors the denominator, which generalizes to the total universe sum in Row 3 (probability) and grid density in Rows 7–9 (chromogeometry).

---

## 🔄 Algebraic Transforms

### Unique Boole Polynumbers
Every logical function has a unique polynomial form (polynumber). For $n$ inputs, a function is represented as a vector of $2^n$ coefficients in $B_2$. Two logic circuits are equivalent if and only if their unique polynumber coefficients match exactly, replacing NP-complete SAT solving with $O(1)$ coordinate comparison.

### The Boole-Möbius Transform ([MobiusTransform.idr](file:///var/home/justin/Projects/Idris2-Boole/src/Boole/MobiusTransform.idr))
A self-inverse linear transform ($T^2 = I$) that maps a function's truth table to its unique Boole polynumber coefficients. 

### Row 1 → Row 2 Progression Bridge ([BooleFraction.idr](file:///var/home/justin/Projects/Idris2-Boole/src/Boole/BooleFraction.idr))
The function `liftToRow2` lifts a `BooleFraction` (with mod-2 $F_2$ coefficients) to a Row 2 integer multiset (with algebraic `BoxInt` coefficients). This maps the digital logic layer directly to the integer polynumber layer, ready for the Möbius shift.

---

## 📁 Module Organization

| Module | Role |
|---|---|
| [Boole.BF2](file:///var/home/justin/Projects/Idris2-Boole/src/Boole/BF2.idr) | Bi-field $B_2$ arithmetic, XOR addition, AND multiplication, `Num` instance. |
| [Boole.BitGate](file:///var/home/justin/Projects/Idris2-Boole/src/Boole/BitGate.idr) | Bit-gate multisets, coordinate evaluation, and `BoxInt` lifting. |
| [Boole.BooleFraction](file:///var/home/justin/Projects/Idris2-Boole/src/Boole/BooleFraction.idr) | The `BooleFraction` type, compile-time triviality proof, and Row 2 bridge. |
| [Boole.MobiusTransform](file:///var/home/justin/Projects/Idris2-Boole/src/Boole/MobiusTransform.idr) | The self-inverse Boole-Möbius transform ($T^2 = I$). |
| [Boole.Polynumber](file:///var/home/justin/Projects/Idris2-Boole/src/Boole/Polynumber.idr) | Multilinear polynumber algebra, evaluation, multiplication, and equivalence checks. |
| [Boole.Circuit](file:///var/home/justin/Projects/Idris2-Boole/src/Boole/Circuit.idr) | Circuit AST representation, primitive/derived gate translation, and complexity counting. |
| [Boole.Bit](file:///var/home/justin/Projects/Idris2-Boole/src/Boole/Bit.idr) | Dependent witness linear types for B₂ values. |
| [Boole.Byte](file:///var/home/justin/Projects/Idris2-Boole/src/Boole/Byte.idr) | B₂ⁿ vector coordinate spaces. |
| [Boole.Syllogism](file:///var/home/justin/Projects/Idris2-Boole/src/Boole/Syllogism.idr) | Classical syllogistic logic (Barbara, Celarent, Ferio) evaluated algebraically. |
| [Boole.Interfaces](file:///var/home/justin/Projects/Idris2-Boole/src/Boole/Interfaces.idr) | Linear logic interfaces (`LConsumable`, `LComonoid`, `LEq`). |

---

## 🛠️ Installation & Pack Integration

To register `idris2-Boole` in your local Pack database, add the following to your `pack.toml`:

```toml
[custom.all.idris2-Boole]
type = "local"
path = "../Idris2-Boole"
ipkg = "idris2-Boole.ipkg"
```

Then add `idris2-Boole` to your `.ipkg` dependency list:

```
depends = base, contrib, linear, idris2-Multiset, idris2-Boole
```

---

## 📚 References

- **Norman J. Wildberger**: *Algebra of Boole* (Mathematical Foundations Lectures 255–280).
- **George Boole (1847)**: *The Mathematical Analysis of Logic*.

---

© Justin Kelly. All rights reserved.
