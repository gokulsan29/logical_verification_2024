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

theorem is_multiple_k_2n (n k : ℕ) (h : IsMultiple k n) (h1 : IsMultiple (2 * k) n) :
  IsMultiple k (2 * n) :=
  by
    induction h with
    | zero k' => sorry
    | add_k k' n' hk'n' ih => sorry
    | mul2 k' n' hk'n' ih => sorry

inductive Star {α : Type} : (α → α → Prop) → α → α → Prop where
  | base (R : α → α → Prop) (a b : α) : R a b → Star R a b
  | refl (R : α → α → Prop) (a : α) : Star R a a
  | trans (R : α → α → Prop) (a b c : α) : Star R a b → Star R b c → Star R a c

theorem star_star_impl_star {α : Type} (R : α → α → Prop) (a b : α) :
  Star (Star R) a b → Star R a b :=
  by
    intro h
    induction h with
    | base a' b' hab => exact hab
    | refl a' => simp [Star.refl]
    | trans a' b' c' hab hbc ihab ihbc => sorry

theorem mod_k_eq_zero (n k : ℕ) (h : n % (2 * k) = 0) :
  n % k = 0 :=
  by
    induction n with
    | zero => sorry
    | succ n' ih => sorry

inductive Vec (α : Type) : ℕ → Type where
  | nil                                : Vec α 0
  | cons (a : α) {n : ℕ} (v : Vec α n) : Vec α (n + 1)

def explicit_length_vec {α : Type} {n : ℕ} (v : Vec α n) :=
  match v with
  | .nil => 0
  | .cons _ vs => 1 + (explicit_length_vec vs)

theorem len_n_impl_cons_n_plus_1 {α : Type} (n : ℕ) (v : Vec α n) (a : α) :
  explicit_length_vec v = n → explicit_length_vec (Vec.cons a v) = n + 1 :=
  by
    intro h
    induction v with
    | nil => sorry
    | @cons a' n' vs ih => sorry

end LoVe
