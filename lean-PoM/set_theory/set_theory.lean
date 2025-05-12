-- set_theory.lean

def twice (f : Nat -> Nat) (a : Nat) :=
f (f a)

#eval println! twice (fun x => x + 2) 10

theorem twiceAdd2 (a: Nat) : twice (fun x => x + 2) a = a + 4 :=
-- True proof is by reflexivity. Lean "symbolically" reduces both sides of the equality until they are identical.
rfl

-- continuing on the page https://lean-lang.org/documentation/tour/ ...here: ...(* + 2)
