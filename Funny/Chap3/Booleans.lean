import Init.Data.Nat.Basic
import Mathlib.Data.Rel

open Std

inductive Bval : Type where
  | true : Bval
  | false : Bval

inductive B : Type where
  | val : Bval → B
  | if_then_else : B → B → B → B

instance : Coe Bval B where
  coe := B.val

inductive Eval : Rel B B where
  | e_if_true : ∀ {t₂ t₃}, Eval (B.if_then_else Bval.true t₂ t₃) t₂
  | e_if_false : ∀ {t₂ t₃}, Eval (B.if_then_else Bval.false t₂ t₃) t₃
  | e_if : ∀ {t₁ t₁' t₂ t₃}, Eval t₁ t₁' → Eval (B.if_then_else t₁ t₂ t₃) (B.if_then_else t₁' t₂ t₃)

theorem values_do_not_eval : ∀ (val : Bval), ¬∃x : B, Eval (B.val val) x := by
  intro v ⟨x, ev⟩
  cases ev

theorem determinancy_of_one_step : ∀ {t t' t''}, (Eval t t') → (Eval t t'') → t' = t'' := by
  intro t t' t'' ev₁ ev₂
  induction ev₁ with
  | e_if_true =>
    cases ev₂ with
    | e_if_true => rfl
    | e_if => contradiction
  | e_if_false =>
    cases ev₂ with
    | e_if_false => rfl
    | e_if => contradiction
  | e_if i₁ =>
    cases ev₂ with
    | e_if_true => contradiction
    | e_if_false => contradiction
    | e_if i₂ => rw [determinancy_of_one_step i₁ i₂]

@[simp]
def is_normal_form (x : B) : Prop := ¬∃y : B, Eval x y

theorem values_are_normal_form : ∀ (v : Bval), is_normal_form (B.val v) := by
  simp [is_normal_form]
  intro v x ev
  cases ev

theorem conditional_not_normal_form : ∀ (a b c), ¬(is_normal_form (B.if_then_else a b c)) := by
  intro a b c
  simp [is_normal_form]
  induction a generalizing b c with
  | val m =>
    cases m with
    | true => exact ⟨ b, Eval.e_if_true ⟩
    | false => exact ⟨ c, Eval.e_if_false ⟩
  | if_then_else a₁ a₂ a₃ ih₁ =>
    have := ih₁ (b := a₂) (c := a₃)
    obtain ⟨ q, hq ⟩ := this
    exact ⟨ _, Eval.e_if hq ⟩

theorem normal_form_is_value : ∀ (x : B), is_normal_form x → ∃y, x = B.val y := by
  intro x nf
  simp at nf
  induction x with
  | val m => use m
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

theorem helper₂ : ∀ x y, is_normal_form x → x ⇒ y → x = y := by
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
  intro t u u' nfu nfu' mse mse'
  have u_value := normal_form_is_value u nfu
  have u'_value := normal_form_is_value u' nfu'
  induction mse with
  | rfl =>
    cases mse' with
    | rfl => rfl
    | single ev =>
      simp at nfu
      exfalso
      exact nfu u' ev
    | trans h₁ h₂ =>
      have x_eq_y := normal_form_only_eval_to_itself _ _ nfu h₁
      rw [x_eq_y] at nfu
      have y_eq_u := normal_form_only_eval_to_itself _ u' nfu h₂
      rw [x_eq_y, y_eq_u]
  | single ev =>
    cases mse' with
    | rfl =>
      simp at nfu'
      exfalso
      exact nfu' _ ev
    | single ev₁ =>
      exact determinancy_of_one_step ev ev₁
    | trans h₁ h₂ =>
      have x_ev_y := MultiStep.single ev
      have x_ev_u' := MultiStep.trans h₁ h₂
      have y_ev_u' := helper x_ev_u' x_ev_y nfu'
      exact helper₂ _ u' nfu y_ev_u'

  | trans h₁ h₂ ih₁ ih₂ =>
    cases mse' with
    | rfl =>
      have u'_eq_y := normal_form_only_eval_to_itself u' _ nfu' h₁
      rw [u'_eq_y] at ih₂
      have  z_eq_y := ih₂ nfu MultiStep.rfl u_value
      rw [z_eq_y, u'_eq_y]
    | single ev₁ =>
      have x_ev_u' := MultiStep.single ev₁
      suffices ∀ {x y z}, x ⇒ y → x ⇒ z → is_normal_form y → z ⇒ y by
        have y_ev_u' := this x_ev_u' h₁ nfu'
        exact ih₂ nfu y_ev_u' u_value
      exact helper
    | trans h₃ h₄ =>
      have x_ev_u' := MultiStep.trans h₃ h₄
      have y_ev_u' := helper x_ev_u' h₁ nfu'
      exact ih₂ nfu y_ev_u' u_value

theorem multi_step_if
  : ∀ {a b c d},
  a ⇒ b →
  B.if_then_else a c d ⇒ B.if_then_else b c d := by
  intro a b c d aeb
  induction aeb with
  | rfl =>
    exact MultiStep.rfl
  | single ev =>
    have := @Eval.e_if _ _ c d ev
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

  have ⟨ y, p ⟩ := normal_form_is_value _ bnf
  cases b with
  | val bool =>
    cases bool with
    | true =>
      left
      have := @Eval.e_if_true c d
      exact MultiStep.single this
    | false =>
      right
      have := @Eval.e_if_false c d
      exact MultiStep.single this
  | if_then_else => contradiction

theorem termination_of_evaluation : ∀ t : B, ∃ u, is_normal_form u ∧ t ⇒ u := by
  intro t
  induction t with
  | val v =>
    have := values_are_normal_form v
    exact ⟨ B.val v, And.intro this MultiStep.rfl ⟩
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
