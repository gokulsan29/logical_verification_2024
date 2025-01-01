import LoVe.LoVelib

set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe

inductive IsMultiple : ℕ → ℕ → Prop where
  | zero (k : ℕ) : IsMultiple k 0
  | add_k (k n : ℕ) : IsMultiple k n → IsMultiple k (n + k)
  | mul2 (k n : ℕ) : IsMultiple (2 * k) n → IsMultiple k n

theorem is_multiple_k_impl_mod_k_eq_0 (k n : ℕ) :
  IsMultiple k n → n % k = 0 :=
  by
    intro h
    induction h with
    | zero k' => rfl
    | add_k k' n' hk'n' ih => simp [ih]
    | mul2 k' n' hk'n' ih => sorry

end LoVe
