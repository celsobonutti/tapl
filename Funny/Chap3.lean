import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Insert
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Card
import Init.Data.Nat.Basic
import Mathlib.Data.Finset.NAry
import Mathlib.Data.Rel

open Std

inductive T : Type where
  | true : T
  | false : T
  | if_then_else : T → T → T → T
  | zero : T
  | succ : T → T
  | pred : T → T
  | is_zero : T → T
  deriving DecidableEq, Ord


def S (n : Nat) : Finset T :=
  match n with
  | 0 => ∅
  | m + 1 => {T.true, T.false, T.zero}
             ∪ (S m).image T.succ
             ∪ (S m).image T.pred
             ∪ (S m).image T.is_zero
             ∪ (S m ×ˢ S m ×ˢ S m).image (λ (x, y, z) => T.if_then_else x y z)

example : T.true ∈ S 1 := by
  simp [S]

-- theorem comulative : ∀ n : Nat, S n ⊆ S (n + 1) := by
--   intro n
--   induction n with
--   | zero => simp [S]
--   | succ n ih =>
--     simp only [S]
--     intro t ht
--     simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
--                Finset.mem_image, Prod.exists]

--     sorry


def T.Constants : T → Finset T
  | T.true => {T.true}
  | T.false => {T.false}
  | T.zero => {T.zero}
  | T.succ x => x.Constants
  | T.pred x => x.Constants
  | T.is_zero x => x.Constants
  | T.if_then_else x y z => x.Constants ∪ y.Constants ∪ z.Constants

def T.size : T → Nat
  | T.true
  | T.false
  | T.zero => 1
  | T.succ x
  | T.pred x
  | T.is_zero x => x.size + 1
  | T.if_then_else x y z => x.size + y.size + z.size + 1

def List.max
  (xs : List Nat)
  (nempty : ¬xs = [] := by simp) : ℕ :=
    match h : xs.max? with
    | some x => x
    | none => by
      have none_implies_empty := List.max?_eq_none_iff.mp h
      contradiction

def T.depth : T → Nat
  | T.true
  | T.false
  | T.zero => 1
  | T.succ x
  | T.pred x
  | T.is_zero x => x.depth + 1
  | T.if_then_else x y z => [x.depth, y.depth, z.depth].max + 1

def T.subterms : T → Finset T
  | T.true
  | T.false
  | T.zero => ∅
  | T.succ x
  | T.pred x
  | T.is_zero x => {x}
  | T.if_then_else x y z => {x, y, z}

theorem Const_number_leq_size : ∀ t : T, t.Constants.card ≤ t.size := by
  intro t
  induction t with
  | true
  | false
  | zero =>
    simp [T.Constants, T.size]
  | is_zero x ih
  | pred x ih
  | succ x ih =>
    simp [T.Constants, T.size]
    apply Nat.le_step ih
  | if_then_else x y z ih₁ ih₂ ih₃ =>
    simp [T.Constants, T.size]
    have := Nat.add_le_add ih₁ ih₂
    have := Nat.add_le_add this ih₃
    have right := Nat.le_succ_of_le this
    have := Finset.card_union_le y.Constants z.Constants
    have p : x.Constants.card + (y.Constants ∪ z.Constants).card ≤ x.Constants.card + y.Constants.card + z.Constants.card := by
      rw [Nat.add_assoc]
      exact Nat.add_le_add_left this x.Constants.card
    have := Finset.card_union_le x.Constants (y.Constants ∪ z.Constants)
    have left := Nat.le_trans this p
    exact Nat.le_trans left right

theorem induction_on_depth (P : T → Prop) :
  (∀ s, (∀ r, r.depth < s.depth → P r) → P s) →
  ∀ s, P s := by
  intro h s
  suffices p : ∀ n, ∀ t : T, t.depth = n → P t by
    exact p s.depth s (refl s.depth)
  intro n
  induction n using Nat.strong_induction_on with
  | h m ih =>
    intro t ht
    apply h t
    intro r r_smaller
    rw [←ht] at ih
    apply ih
    exact r_smaller
    rfl

theorem induction_on_size (P : T → Prop) :
  (∀ s, (∀ r, r.size < s.size → P r) → P s) →
  ∀ s, P s :=
  by
  intro h s
  suffices Q : ∀ n, ∀ t : T, t.size = n → P t by
    apply Q s.size s (rfl)
  intro n
  induction n using Nat.strong_induction_on with
  | h m hi =>
  intro t ht
  apply h
  intro r hr
  rw [←ht] at hi
  apply hi
  exact hr
  rfl

theorem subterms_smaller_size : (t : T) → (st : T) → st ∈ t.subterms → st.size < t.size := by
  intro t st
  cases t with
  | true
  | false
  | zero =>
    simp [T.subterms]
  | succ x
  | pred x
  | is_zero x =>
    simp [T.size, T.subterms]
    intro eq
    rw [eq]
    apply Nat.lt_add_one
  | if_then_else x y z =>
    simp [T.size, T.subterms]
    intro eq_or
    rcases eq_or with h | h | h <;> (subst h; omega)

theorem structural_induction (P : T → Prop) :
  (∀ s, (∀ r ∈ s.subterms, P r) → P s) →
  ∀ s, P s := by
  intro h
  apply induction_on_size
  intro s hi
  apply h
  intro r hr
  apply hi
  apply subterms_smaller_size
  exact hr

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
  | rfl : ∀ x, MultiStep x x
  | single : ∀ x y, Eval x y → MultiStep x y
  | trans : ∀ x y z, MultiStep x y → MultiStep y z → MultiStep x z

infixl:50 "⇒" => MultiStep

theorem normal_form_only_eval_to_itself : ∀ x y, is_normal_form x → MultiStep x y → x = y := by
  intro x y nfx mse
  induction mse with
  | rfl _ =>
    rfl
  | single x₁ y₁ ev =>
    simp at nfx
    exfalso
    exact nfx y₁ ev
  | trans x₁ x₂ x₃ mse₁ mse₂ ih₁ ih₂ =>
    have eq₁ := ih₁ nfx
    rw [eq₁] at nfx
    have eq₂ := ih₂ nfx
    rw [eq₁, eq₂]

theorem mid_step : ∀ {x y z}, x ⇒ y → Eval x z → x = y ∨ z ⇒ y := by
  intro x y z mse ev
  induction mse with
  | rfl _ => left; rfl
  | single _ _ ev₁ =>
    right
    rw [determinancy_of_one_step ev ev₁]
    exact MultiStep.rfl _
  | trans a b c mse₁ mse₂ ih₁ ih₂ =>
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
      right; exact MultiStep.trans _ _ _ h mse₂

theorem helper : ∀ {x y z}, x ⇒ y → x ⇒ z → is_normal_form y → z ⇒ y := by
  intro x y z x_e_y x_e_z nfy
  induction x_e_z with
  | rfl a => exact x_e_y
  | single a b ih =>
    cases x_e_y with
    | rfl _ =>
      simp at nfy
      exfalso
      exact nfy b ih
    | single a₁ b₁ ih₁ =>
      rw [determinancy_of_one_step ih ih₁]
      exact MultiStep.rfl y
    | trans x₁ x₂ x₃ mse₁ mse₂ =>
      cases mid_step mse₁ ih with
      | inl h₁ =>
        rw [←h₁] at mse₂
        cases mid_step mse₂ ih with
        | inl h₂ =>
          exfalso
          simp at nfy
          rw [h₂] at ih
          exact nfy b ih
        | inr h₂ =>
          exact h₂
      | inr h₁ =>
        exact MultiStep.trans _ _ _ h₁ mse₂
  | trans a b c mse₁ mse₂ ih₁ ih₂ =>
    have := ih₁ x_e_y
    exact ih₂ this

theorem helper₂ : ∀ x y, is_normal_form x → x ⇒ y → x = y := by
  intro x y nfx xey
  induction xey with
  | rfl => rfl
  | single a b ev =>
    simp at nfx
    exfalso
    exact nfx b ev
  | trans a b c mse₁ mse₂ ih₁ ih₂ =>
    rw [ih₁ nfx]
    rw [ih₁ nfx] at nfx
    exact ih₂ nfx

theorem uniqueness_of_normal_forms : ∀ t u u', is_normal_form u → is_normal_form u' → t ⇒ u → t ⇒ u' → u = u' := by
  intro t u u' nfu nfu' mse mse'
  have u_value := normal_form_is_value u nfu
  have u'_value := normal_form_is_value u' nfu'
  induction mse with
  | rfl _ =>
    cases mse' with
    | rfl _ => rfl
    | single _ _ ev =>
      simp at nfu
      exfalso
      exact nfu u' ev
    | trans x y z h₁ h₂ =>
      have x_eq_y := normal_form_only_eval_to_itself _ y nfu h₁
      rw [x_eq_y] at nfu
      have y_eq_u := normal_form_only_eval_to_itself _ u' nfu h₂
      rw [x_eq_y, y_eq_u]
  | single x y ev =>
    cases mse' with
    | rfl _ =>
      simp at nfu'
      exfalso
      exact nfu' y ev
    | single _ _ ev₁ =>
      exact determinancy_of_one_step ev ev₁
    | trans a b c h₁ h₂ =>
      have x_ev_y := MultiStep.single _ _ ev
      have x_ev_u' := MultiStep.trans _ _ _ h₁ h₂
      have y_ev_u' := helper x_ev_u' x_ev_y nfu'
      exact helper₂ y u' nfu y_ev_u'

  | trans x y z h₁ h₂ ih₁ ih₂ =>
    cases mse' with
    | rfl _ =>
      have u'_eq_y := normal_form_only_eval_to_itself u' y nfu' h₁
      rw [u'_eq_y] at ih₂
      have  z_eq_y := ih₂ nfu (MultiStep.rfl y) u_value
      rw [z_eq_y, u'_eq_y]
    | single a b ev₁ =>
      have x_ev_u' : x ⇒ u' := MultiStep.single x u' ev₁
      suffices ∀ {x y z}, x ⇒ y → x ⇒ z → is_normal_form y → z ⇒ y by
        have y_ev_u' := this x_ev_u' h₁ nfu'
        exact ih₂ nfu y_ev_u' u_value
      exact helper
    | trans a b c h₃ h₄ =>
      have x_ev_u' := MultiStep.trans _ _ _ h₃ h₄
      have y_ev_u' := helper x_ev_u' h₁ nfu'
      exact ih₂ nfu y_ev_u' u_value
