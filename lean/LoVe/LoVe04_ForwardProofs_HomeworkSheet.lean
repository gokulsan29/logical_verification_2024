/- Copyright © 2018–2024 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe03_BackwardProofs_ExerciseSheet


/- # LoVe Homework 4 (10 points): Forward Proofs

Homework must be done individually.

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1 (4 points): Logic Puzzles

Consider the following tactical proof: -/

theorem about_Impl :
  ∀a b : Prop, ¬ a ∨ b → a → b :=
  by
    intros a b hor ha
    apply Or.elim hor
    { intro hna
      apply False.elim
      apply hna
      exact ha }
    { intro hb
      exact hb }

/- 1.1 (2 points). Prove the same theorem again, this time by providing a proof
term.

Hint: There is an easy way. -/

theorem about_Impl_term :
  ∀a b : Prop, ¬ a ∨ b → a → b :=
  fun a : Prop ↦ fun b : Prop ↦ fun hnab : ¬a ∨ b ↦
    fun ha : a ↦ Or.elim hnab (fun hna : ¬a ↦ (False.elim (hna ha))) (fun hb : b ↦ hb)

/- 1.2 (2 points). Prove the same theorem again, this time by providing a
structured proof, with `fix`, `assume`, and `show`. -/

theorem about_Impl_struct :
  ∀a b : Prop, ¬ a ∨ b → a → b :=
  fix a : Prop
  fix b : Prop
  assume hnab : ¬a ∨ b
  assume ha : a
  show b from
    Or.elim hnab
    (
      assume hna : ¬a
      False.elim (hna ha)
    )
    (
      assume hb : b
      hb
    )

/- ## Question 2 (6 points): Connectives and Quantifiers

2.1 (3 points). Supply a structured proof of the commutativity of `∨` under a
`∀` quantifier, using no other theorems than the introduction and elimination
rules for `∀`, `∨`, and `↔`. -/

theorem Or_comm_under_All {α : Type} (p q : α → Prop) :
  (∀x, p x ∨ q x) ↔ (∀x, q x ∨ p x) :=
  Iff.intro
  (
    assume hall : ∀x, p x ∨ q x
    fix x : α
    Or.elim (hall x)
    (
      assume hpx : p x
      show q x ∨ p x from
        Or.inr hpx
    )
    (
      assume hqx : q x
      show q x ∨ p x from
        Or.inl hqx
    )
  )
  (
    assume hall : ∀x, q x ∨ p x
    fix x : α
    Or.elim (hall x)
    (
      assume hqx : q x
      show p x ∨ q x from
        Or.inr hqx
    )
    (
      assume hpx : p x
      show p x ∨ q x from
        Or.inl hpx
    )
  )

/- 2.2 (3 points). We have proved or stated three of the six possible
implications between `ExcludedMiddle`, `Peirce`, and `DoubleNegation` in the
exercise of lecture 3. Prove the three missing implications using structured
proofs, exploiting the three theorems we already have. -/

namespace BackwardProofs

#check Peirce_of_EM
#check DN_of_Peirce
#check SorryTheorems.EM_of_DN

theorem Peirce_of_DN :
  DoubleNegation → Peirce :=
  assume hdn : DoubleNegation
  show Peirce from
    Peirce_of_EM (SorryTheorems.EM_of_DN hdn)

theorem EM_of_Peirce :
  Peirce → ExcludedMiddle :=
  assume hp : Peirce
  SorryTheorems.EM_of_DN (DN_of_Peirce hp)

theorem dn_of_em :
  ExcludedMiddle → DoubleNegation :=
  assume hem : ExcludedMiddle
  DN_of_Peirce (Peirce_of_EM hem)

end BackwardProofs

end LoVe
