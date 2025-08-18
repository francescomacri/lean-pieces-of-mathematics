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

When you write p \wedge q \equiv q \wedge p in informal math, Lean formalizes this as p \wedge q \iff q \wedge p (p ∧ q ↔ q ∧ p), because ↔ is the formal, constructive way to express logical equivalence inside the system. Similarly this is valid for the disjunction.
-/

-- Theorems in Lean's mathematics library.
import Mathlib.Logic.Basic

-- Declaring the propositions p and q as variables.
-- "variable" is a Lean keyword to declare variables or parameters.
-- (P Q : Prop) declares two variables, P and Q, both of type Prop (propositions).
variable (P Q : Prop)

/-
  Theorem: Commutativity of conjunction (and)
  Statement: p ∧ q is logically equivalent to q ∧ p
  Proof outline: From p ∧ q, we get p and q individually, then swap their order.
-/

-- "example" is a keyword in Lean used to state a proposition and prove it immediately.
-- ":= by" starts the proof using tactic mode (interactive proof style).
-- "apply" is a tactic that tries to prove the goal by matching it to the conclusion of a given theorem or constructor.
-- "Iff.intro" is a constructor of the ↔ (\iff) type. It comes from Lean's core library (Init.Logic).

/-
Iff.intro requires proving both directions separately:
  - From P ∧ Q to Q ∧ P
  - From Q ∧ P to P ∧ Q
"intro h" this tactic breaks the goal into two subgoals for each direction.
· starts a new subproof (tactic block).
intro h introduces the assumption (hypothesis) from the implication to the context and names it h.
Here, h : P ∧ Q for the first direction.
intro is a basic tactic from Lean’s tactic framework.
    exact And.intro h.right h.left
exact tells Lean to finish this goal by providing this term exactly.
And.intro is a constructor for the ∧ (and) type, also from Lean’s core library.
It takes two arguments: proofs of Q and P respectively (to build Q ∧ P).
h.right extracts the right part Q from the hypothesis h : P ∧ Q.
h.left extracts the left part P from h.
So this line constructs Q ∧ P from h.
  · intro h
    exact And.intro h.right h.left
This is the second subproof for the other direction.
It works symmetrically to the first.

-/
example : P ∧ Q ↔ Q ∧ P := by
  apply Iff.intro
  · intro h
    exact And.intro h.right h.left
  · intro h
    exact And.intro h.right h.left

/-
  Theorem: Commutativity of disjunction (or)
  Statement: P ∨ Q is logically equivalent to Q ∨ P
  Proof outline: From P ∨ Q, we use cases to show Q ∨ P by swapping the order.
-/

/-
cases is a tactic to do case analysis on an inductive type (here P ∨ Q).

P ∨ Q is an inductive type with two constructors:

Or.inl means the left side P holds.

Or.inr means the right side Q holds.
The with syntax names the cases and their associated variables.

In the inl case, p : P, we construct Q ∨ P by putting p on the right (Or.inr p).

In the inr case, q : Q, we construct Q ∨ P by putting q on the left (Or.inl q).

This swaps the order of the disjunction.
-/

example : P ∨ Q ↔ Q ∨ P := by
  apply Iff.intro
  · intro h
    cases h with
    | inl p =>
      exact Or.inr p
    | inr q =>
      exact Or.inl q
  · intro h
    cases h with
    | inl q =>
      exact Or.inr q
    | inr p =>
      exact Or.inl p


/- List of key commands used in this .lean-file

variable
Declares variables or parameters used in proofs.
Origin: Lean core language.

example
States a proposition and proves it immediately.
Origin: Lean core language.

apply
Uses a theorem or constructor to transform the current goal into subgoals.
Origin: Lean tactic framework.

Iff.intro
Constructor for the logical equivalence ↔ (iff). It requires proving both directions separately.
Origin: Lean core library (Init.Logic).

intro
Introduces assumptions (hypotheses) for implications or universal quantifications in the proof context.
Origin: Lean tactic framework.

exact
Provides the exact term that proves the current goal, completing that proof branch.
Origin: Lean tactic framework.

And.intro
Constructor for conjunction ∧ (and). Takes proofs of both parts to build the conjunction.
Origin: Lean core library (Init.Logic).

cases
Performs case analysis on an inductive type (e.g., disjunction or sums).
Origin: Lean tactic framework.

Or.inl and Or.inr
Constructors for disjunction ∨ (or). Or.inl corresponds to the left case, Or.inr to the right case.
Origin: Lean core library (Init.Logic).

-/
