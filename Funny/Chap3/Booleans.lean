import Init.Data.Nat.Basic
import Mathlib.Data.Rel

open Std

inductive B : Type where
  | true : B
  | false : B
  | if_then_else : B → B → B → B

inductive IsValue : B → Prop where
  | true : IsValue B.true
  | false : IsValue B.false

theorem IsValue.cases : ∀ {x}, IsValue x → x = B.true ∨ x = B.false := by
  intro x is_value
  cases is_value <;> simp

inductive Eval : Rel B B where
  | if_true : ∀ {t₂ t₃}, Eval (B.if_then_else B.true t₂ t₃) t₂
  | if_false : ∀ {t₂ t₃}, Eval (B.if_then_else B.false t₂ t₃) t₃
  | if_ : ∀ {t₁ t₁' t₂ t₃}, Eval t₁ t₁' → Eval (B.if_then_else t₁ t₂ t₃) (B.if_then_else t₁' t₂ t₃)

theorem values_do_not_eval : ∀ (x : B), {_ : IsValue x} → ¬∃y : B, Eval x y := by
  intro x is_value ⟨y, ev⟩
  have := is_value.cases
  cases ev <;> contradiction

theorem determinancy_of_one_step : ∀ {t t' t''}, (Eval t t') → (Eval t t'') → t' = t'' := by
  intro t t' t'' ev₁ ev₂
  induction ev₁ with
  | if_true =>
    cases ev₂ with
    | if_true => rfl
    | if_ => contradiction
  | if_false =>
    cases ev₂ with
    | if_false => rfl
    | if_ => contradiction
  | if_ i₁ =>
    cases ev₂ with
    | if_true => contradiction
    | if_false => contradiction
    | if_ i₂ => rw [determinancy_of_one_step i₁ i₂]

@[simp]
def is_normal_form (x : B) : Prop := ¬∃y : B, Eval x y

theorem values_are_normal_form : ∀ v, (_ : IsValue v := by simp) → is_normal_form v := by
  simp [is_normal_form]
  intro v is_value x ev
  cases ev <;> contradiction

theorem conditional_not_normal_form : ∀ (a b c), ¬(is_normal_form (B.if_then_else a b c)) := by
  intro a b c
  simp [is_normal_form]
  induction a generalizing b c with
  | true =>
    exact ⟨ b, Eval.if_true ⟩
  | false =>
    exact ⟨ c, Eval.if_false ⟩
  | if_then_else a₁ a₂ a₃ ih₁ =>
    have := ih₁ (b := a₂) (c := a₃)
    obtain ⟨ q, hq ⟩ := this
    exact ⟨ _, Eval.if_ hq ⟩

theorem normal_form_is_value : ∀ (x : B), is_normal_form x → IsValue x := by
  intro x nf
  simp at nf
  induction x with
  | true => exact IsValue.true
  | false => exact IsValue.false
  | if_then_else a b c =>
    exfalso
    have not_nf := conditional_not_normal_form a b c
    simp at not_nf
    obtain ⟨ y, ev ⟩ := not_nf
    exact nf y ev

inductive MultiStep : Rel B B where
  | rfl : ∀ {x}, MultiStep x x
  | single : ∀ {x y}, Eval x y → MultiStep x y
  | trans : ∀ {x y z}, MultiStep x y → MultiStep y z → MultiStep x z

infixl:50 "⇒" => MultiStep

theorem normal_form_only_eval_to_itself : ∀ x y, is_normal_form x → MultiStep x y → x = y := by
  intro x y nfx mse
  induction mse with
  | rfl =>
    rfl
  | single ev =>
    simp at nfx
    exfalso
    exact nfx _ ev
  | trans mse₁ mse₂ ih₁ ih₂ =>
    have eq₁ := ih₁ nfx
    rw [eq₁] at nfx
    have eq₂ := ih₂ nfx
    rw [eq₁, eq₂]

theorem mid_step : ∀ {x y z}, x ⇒ y → Eval x z → x = y ∨ z ⇒ y := by
  intro x y z mse ev
  induction mse with
  | rfl => left; rfl
  | single ev₁ =>
    right
    rw [determinancy_of_one_step ev ev₁]
    exact MultiStep.rfl
  | trans mse₁ mse₂ ih₁ ih₂ =>
    cases ih₁ ev with
    | inl h =>
      rw [h] at ev
      cases ih₂ ev with
      | inl h₁ =>
        rw [h, h₁]
        left; rfl
      | inr h₁ =>
        right; exact h₁
    | inr h =>
      right; exact MultiStep.trans h mse₂

theorem helper : ∀ {x y z}, x ⇒ y → x ⇒ z → is_normal_form y → z ⇒ y := by
  intro x y z x_e_y x_e_z nfy
  induction x_e_z with
  | rfl => exact x_e_y
  | single ih =>
    cases x_e_y with
    | rfl =>
      simp at nfy
      exfalso
      exact nfy _ ih
    | single ih₁ =>
      rw [determinancy_of_one_step ih ih₁]
      exact MultiStep.rfl
    | trans mse₁ mse₂ =>
      cases mid_step mse₁ ih with
      | inl h₁ =>
        rw [←h₁] at mse₂
        cases mid_step mse₂ ih with
        | inl h₂ =>
          exfalso
          simp at nfy
          rw [h₂] at ih
          exact nfy _ ih
        | inr h₂ =>
          exact h₂
      | inr h₁ =>
        exact MultiStep.trans h₁ mse₂
  | trans mse₁ mse₂ ih₁ ih₂ =>
    have := ih₁ x_e_y
    exact ih₂ this

theorem helper₂ : ∀ {x y}, is_normal_form x → x ⇒ y → x = y := by
  intro x y nfx xey
  induction xey with
  | rfl => rfl
  | single ev =>
    simp at nfx
    exfalso
    exact nfx _ ev
  | trans mse₁ mse₂ ih₁ ih₂ =>
    rw [ih₁ nfx]
    rw [ih₁ nfx] at nfx
    exact ih₂ nfx

theorem uniqueness_of_normal_forms : ∀ t u u', is_normal_form u → is_normal_form u' → t ⇒ u → t ⇒ u' → u = u' := by
  intro t u u' nfu nfu' t_to_u t_to_u'
  have u_to_u' := helper t_to_u' t_to_u nfu'
  exact helper₂ nfu u_to_u'

theorem multi_step_if
  : ∀ {a b c d},
  a ⇒ b →
  B.if_then_else a c d ⇒ B.if_then_else b c d := by
  intro a b c d aeb
  induction aeb with
  | rfl =>
    exact MultiStep.rfl
  | single ev =>
    have := @Eval.if_ _ _ c d ev
    exact MultiStep.single this
  | trans h₁ h₂ ih₁ ih₂ =>
    exact MultiStep.trans ih₁ ih₂

theorem multi_step_if_then_else
  : ∀ {a b c d},
  a ⇒ b →
  is_normal_form b →
  B.if_then_else a c d ⇒ c ∨ B.if_then_else a c d ⇒ d := by
  intro a b c d aeb bnf
  have msi := @multi_step_if a b c d aeb
  suffices B.if_then_else b c d ⇒ c ∨ B.if_then_else b c d ⇒ d by
    cases this with
    | inl x =>
      left
      exact MultiStep.trans msi x
    | inr x =>
      right
      exact MultiStep.trans msi x

  have is_value_b := normal_form_is_value _ bnf
  cases b with
  | true =>
    left
    have := @Eval.if_true c d
    exact MultiStep.single this
  | false =>
      right
      have := @Eval.if_false c d
      exact MultiStep.single this
  | if_then_else => contradiction

theorem termination_of_evaluation : ∀ t : B, ∃ u, is_normal_form u ∧ t ⇒ u := by
  intro t
  induction t with
  | true =>
    have := values_are_normal_form B.true IsValue.true
    exact ⟨ B.true, And.intro this MultiStep.rfl ⟩
  | false =>
    have := values_are_normal_form B.false IsValue.false
    exact ⟨ B.false, And.intro this MultiStep.rfl ⟩
  | if_then_else x y z ih₁ ih₂ ih₃ =>
    have ⟨ cond_value, cond_nf ⟩ := ih₁
    have := @multi_step_if_then_else x _ y z cond_nf.right cond_nf.left
    cases this with
    | inl h₁ =>
      have ⟨ cond_value₁, cond_nf₁ ⟩ := ih₂
      have := MultiStep.trans h₁ cond_nf₁.right
      exact ⟨ cond_value₁, And.intro cond_nf₁.left this ⟩
    | inr h₁ =>
      have ⟨ cond_value₁, cond_nf₁ ⟩ := ih₃
      have := MultiStep.trans h₁ cond_nf₁.right
      exact ⟨ cond_value₁, And.intro cond_nf₁.left this ⟩
