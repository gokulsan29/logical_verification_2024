/- Copyright © 2018–2024 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe01_TypesAndTerms_Demo


/- # LoVe Exercise 1: Types and Terms

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1: Terms

Complete the following definitions, by replacing the `sorry` markers by terms
of the expected type.

Hint: A procedure for doing so systematically is described in Section 1.4 of
the Hitchhiker's Guide. As explained there, you can use `_` as a placeholder
while constructing a term. By hovering over `_`, you will see the current
logical context. -/

def I : α → α :=
  fun a ↦ a

def K : α → β → α :=
  fun a b ↦ a

def C : (α → β → γ) → β → α → γ :=
  fun a b c ↦  a c b

def projFst : α → α → α :=
  fun a _ ↦  a

/- Give a different answer than for `projFst`. -/

def projSnd : α → α → α :=
  fun _ b ↦ b

def someNonsense : (α → β → γ) → α → (α → γ) → β → γ :=
  fun _ b c _ ↦ c b


/- ## Question 2: Typing Derivation

Show the typing derivation for your definition of `C` above, on paper or using
ASCII or Unicode art. You might find the characters `–` (to draw horizontal
bars) and `⊢` useful. -/

-- write your solution in a comment here or on paper

/-

--------------------------------------------- (Var)   ----------------------------------- (Var)
a : α → β → γ, b : β, c : α ⊢ a : a → (β → γ)         a : α → β → γ, b : β, c : α ⊢ c : α
----------------------------------------------------------------------------------------- (App)
a : α → β → γ, b : β, c : α ⊢ a c : β → γ

----------------------------------------- (App)   ----------------------------------- (Var)
a : α → β → γ, b : β, c : α ⊢ a c : β → γ         a : α → β → γ, b : β, c : α ⊢ b : β
---------------------------------------------------------------------------------- (App)
a : α → β → γ, b : β, c : α ⊢ ((a c) b) : γ
--------------------------------------------------------------------- (Fun)
⊢ (fun a : α → β → γ b : β c : α ↦ a c b) : (α → β → γ) → β → α → γ
-/


end LoVe
