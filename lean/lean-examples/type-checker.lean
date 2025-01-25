inductive Expr where
  | nat : Nat → Expr
  | plus : Expr → Expr → Expr
  | bool : Bool → Expr
  | and : Expr → Expr → Expr

inductive Ty where -- Type is a keyword
  | nat
  | bool

inductive HasType : Expr → Ty → Prop
  | nat : HasType (.nat v) .nat
  | plus : HasType a .nat → HasType b .nat → HasType (.plus a b) .nat
  | bool : HasType (.bool v) .nat
  | and : HasType a .bool → HasType b .bool → HasType (.and a b) .bool

theorem HasType.det : HasType e t₁ → HasType e t₂ → t₁ = t₂ :=
  by
    intro h₁ h₂
    cases h₁ with
    | nat => cases h₂; rfl
    | plus ha hb => cases h₂; rfl
    | bool => cases h₂; rfl
    | and ha hb => cases h₂; rfl
