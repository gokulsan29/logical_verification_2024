namespace MySet
def Set (α : Type) : Type :=  α → Prop

def emptyset {α : Type} : Set α := fun (_ : α) ↦ False
def φ {α : Type} : Set α := fun (_ : α) ↦ False

theorem not_belongs_to_empty {α : Type} (x : α) :
  φ x = False :=
  by
    rfl

def union {α : Type} (a b : Set α) (x : α) :=
  (a x) ∨ (b x)

infixr:50 " ⋃ " => union

def intersection {α : Type} (a b : Set α) (x : α) :=
  (a x) ∧ (b x)

infixr:50 " ⋂ " => intersection

theorem if_x_in_a_then_x_in_a_union_b {α : Type} (a b : Set α) (x : α) : 
  a x → (a ⋃ b) x :=
  by
    intro hax
    simp [union]
    exact Or.inl hax

theorem if_x_in_b_then_x_in_a_union_b {α : Type} (a b : Set α) (x : α) : 
  b x → (a ⋃ b) x :=
  by
    intro hbx
    simp [union]
    exact Or.inr hbx

theorem if_x_in_a_int_b_then_x_in_a {α : Type} (a b : Set α) (x : α) :
  (a ⋂ b) x → a x :=
  by
    intro hint
    rw [intersection] at hint
    apply And.left hint

theorem if_x_in_a_int_b_then_x_in_b {α : Type} (a b : Set α) (x : α) :
  (a ⋂ b) x → b x :=
  by
    intro hint
    rw [intersection] at hint
    apply And.right hint

theorem union_comm {α : Type} (a b : Set α) :
  (a ⋃ b) = (b ⋃ a) :=
  by
    apply funext
    intro x
    apply propext
    simp [union]
    exact or_comm

theorem inter_comm {α : Type} (a b : Set α) :
  (a ⋂ b) = (b ⋂ a) :=
  by
    apply funext
    intro x
    apply propext
    simp [intersection]
    exact and_comm

theorem inter_empty_eq_empty {α : Type} (a : Set α) :
  (a ⋂ φ) = φ :=
  by
    apply funext
    intro x
    apply propext
    simp [intersection, φ]

theorem union_empty_eq_a {α : Type} (a : Set α) :
  (a ⋃ φ) = a :=
  by
    apply funext
    intro x
    apply propext
    simp [union, φ]

def subset {α : Type} (a a' : Set α) := ∀(x : α), a x → a' x 

infixr:50 " ⊆ " => subset

def set_eq {α : Type} (a a' : Set α) := ∀(x : α), a x ↔ a' x

theorem if_a_sub_a'_then_a_u_b_sub_a'_u_b {α : Type} :
  ∀(a a' b : Set α), (a ⊆ a') → (a ⋃ b) ⊆ (a' ⋃ b) :=
  by
    intro a a' b
    intro hsub
    simp [subset]
    intro x
    simp [union]
    intro hunion
    apply Or.elim hunion
    {
      intro hax
      apply Or.inl
      apply hsub
      exact hax
    }
    {
      intro hbx
      exact Or.inr hbx
    }

theorem if_a_sub_a'_then_a_n_b_sub_a'_n_b {α : Type} :
  ∀(a a' b : Set α), (a ⊆ a') → (a ⋂ b) ⊆ (a' ⋂ b) :=
  by
    intro a a' b
    intro hsub
    simp [subset]
    intro x
    simp [intersection]
    intro hax
    intro hbx
    apply And.intro
    {
      apply hsub
      exact hax
    }
    {
      exact hbx
    }

def cartesian_product {α β : Type} (a : Set α) (b : Set β) (c : α × β) :=
  a c.1 ∧ b c.2

infixr:50 " × " => cartesian_product

theorem a_b_iff_cart_prod {α β : Type} (a : Set α) (b : Set β) :
  ∀(x : α) (y : β), (a x ∧ b y) ↔ ((a × b) (x, y)) :=
  by
    sorry

end MySet
