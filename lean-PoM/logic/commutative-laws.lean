-- commutative-laws.lean

/-
  Commutative Laws in Logic
  Author: Francesco Macrì

This file proves the commutative equivalences for conjunction and disjunction:
  - p ∧ q ↔ q ∧ p
  - p ∨ q ↔ q ∨ p

Symbols used:

  - ↔ : logical equivalence (lean command: \iff)
  - ∧ : logical and (conjunction) (lean command: \and)
  - ∨ : logical or (disjunction, not exclusive) (lean command: \wedge)

-/

-- theorems in Lean's mathematics library
-- import Mathlib.Logic.Basic

-- Declaring the propositions p and q as variables
variable (P Q : Prop)

/-
  Theorem: Commutativity of conjunction (and)
  Statement: p ∧ q is logically equivalent to q ∧ p
  Proof outline: From p ∧ q, we get p and q individually, then swap their order.
-/

example : p ∧ q ↔ q ∧ p := by
  exact not_and_or
