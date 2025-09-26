import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Insert
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Card
import Init.Data.Nat.Basic
import Mathlib.Data.Finset.NAry
import Mathlib.Data.Rel
import Mathlib.Data.Real.Basic

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

def T.Constants : T → Finset T
  | T.true => {T.true}
  | T.false => {T.false}
  | T.zero => {T.zero}
  | T.succ x => x.Constants
  | T.pred x => x.Constants
  | T.is_zero x => x.Constants
  | T.if_then_else x y z => x.Constants ∪ y.Constants ∪ z.Constants

@[simp]
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

@[simp]
def is_bool (t : T) : Prop :=
  match t with
  | T.true | T.false => True
  | _ => False

@[simp]
def is_number (t : T) : Prop :=
  match t with
  | T.zero => True
  | T.succ n => is_number n
  | _ => false


theorem is_number_succ : (t : T) → is_number t → is_number (T.succ t) := by
  intro t is_number_t
  simp [is_number]
  exact is_number_t

@[simp]
def is_value (t : T) : Prop :=
  is_bool t ∨ is_number t

open T in
inductive Eval : Rel T T where
  | if_true : ∀ {t₂ t₃}, Eval (if_then_else true t₂ t₃) t₂
  | if_false : ∀ {t₂ t₃}, Eval (if_then_else false t₂ t₃) t₃
  | if_ : ∀ {t₁ t₁' t₂ t₃}, Eval t₁ t₁' → Eval (if_then_else t₁ t₂ t₃) (if_then_else t₁' t₂ t₃)
  | succ : ∀ {t t'}, Eval t t' → Eval (succ t) (succ t')
  | pred_zero : Eval (pred zero) zero
  | pred_succ : ∀ {t}, {_ : is_number t} → Eval (pred (succ t)) t
  | pred : ∀ {t t'}, Eval t t' → Eval (pred t) (pred t')
  | is_zero_zero : Eval (is_zero zero) true
  | is_zero_succ : ∀ {t}, {_ : is_number t} → Eval (is_zero (succ t)) false
  | is_zero : ∀ {t t'}, Eval t t' → Eval (is_zero t) (is_zero t')

@[simp]
def is_normal_form (x : T) : Prop := ¬∃y : T, Eval x y

@[simp]
def is_stuck (x : T) : Prop := is_normal_form x ∧ ¬is_value x

theorem succ_is_not_zero : ∀ {t₁ t₂}, Eval (T.succ t₁) t₂ → ¬(t₂ = T.zero) := by
  intro t₁ t₂ ev₁ eq
  rw [eq] at ev₁
  cases ev₁

theorem booleans_do_not_eval : ∀ (x : T), (_ : is_bool x := by simp) → is_normal_form x := by
  intro x is_bool ⟨y, ev⟩
  cases x with
  | true
  | false => cases ev
  | is_zero
  | pred
  | if_then_else
  | zero
  | succ =>
    simp_all

theorem succ_x_is_number_implies_x_is_number : ∀ {x : T}, is_number (T.succ x) → is_number x := by
  intro y is_number_y
  simp at is_number_y
  exact is_number_y

theorem numbers_do_not_eval : ∀ (x : T), {_ : is_number x} → is_normal_form x := by
  intro x x_is_number ⟨y, ev⟩
  cases x with
  | true
  | false
  | is_zero
  | pred
  | if_then_else => simp_all
  | zero => cases ev
  | succ m =>
    have : is_number m := succ_x_is_number_implies_x_is_number x_is_number
    cases ev with
      | succ ev₁ =>
        have := @numbers_do_not_eval _ this
        apply this ⟨ _, ev₁ ⟩


theorem values_do_not_eval : ∀ (x : T), {_ : is_value x} → is_normal_form x := by
  intro x is_value
  if h₁ : is_number x then
    exact @numbers_do_not_eval x h₁
  else if h₂ : is_bool x then
    exact @booleans_do_not_eval x h₂
  else
    cases is_value with
    | inl | inr => contradiction

theorem determinancy_of_one_step : ∀ {t t' t''}, (Eval t t') → (Eval t t'') → t' = t'' := by
   intro t t' t'' ev₁ ev₂
   cases t with
   | true
   | false
   | zero => cases ev₁
   | succ n =>
     cases ev₁ with
     | succ ev₃ =>
       cases ev₂ with
       | succ ev₄ =>
         have := determinancy_of_one_step ev₃ ev₄
         rw [this]
   | pred n =>
     cases ev₁ with
     | pred ev₃ =>
       cases ev₂ with
       | pred ev₄ =>
         have := determinancy_of_one_step ev₃ ev₄
         rw [this]
       | @pred_succ _ is_number =>
         have := is_number_succ t'' is_number
         have := @numbers_do_not_eval _ this
         exfalso
         exact this ⟨_, ev₃⟩
       | pred_zero => contradiction
     | pred_zero =>
       cases ev₂ with
       | pred => contradiction
       | pred_zero => rfl
     | @pred_succ _ is_number =>
       cases ev₂ with
       | @pred t₃ t₄ ev₃ =>
         have := is_number_succ _ is_number
         have := @numbers_do_not_eval _ this
         exfalso
         exact this ⟨_, ev₃⟩
       | pred_succ => rfl
   | is_zero n =>
     cases ev₁ with
     | is_zero_zero =>
       cases ev₂ with
       | is_zero_zero => rfl
       | is_zero ev₃ =>
         have : is_number T.zero := by simp
         have := @numbers_do_not_eval _ this
         exfalso
         exact this ⟨_, ev₃⟩
     | @is_zero_succ _ is_number =>
       cases ev₂ with
       | is_zero ev₃ =>
         have := is_number_succ _ is_number
         exfalso
         exact @numbers_do_not_eval _ this ⟨_, ev₃⟩
       | is_zero_succ => rfl
     | is_zero ev₃ =>
       cases ev₂ with
       | is_zero ev₄ =>
         have := determinancy_of_one_step ev₃ ev₄
         rw [this]
       | @is_zero_succ _ is_number =>
         have := is_number_succ _ is_number
         exfalso
         exact @numbers_do_not_eval _ this ⟨_, ev₃⟩
       | is_zero_zero =>
         have : is_number T.zero := by simp
         exfalso
         exact @numbers_do_not_eval _ this ⟨_, ev₃⟩
   | if_then_else x y z =>
     cases ev₁ with
     | if_ ev₃ =>
       cases ev₂ with
       | if_ ev₄ =>
         have := determinancy_of_one_step ev₃ ev₄
         rw [this]
       | if_false =>
         exfalso
         exact (booleans_do_not_eval _) ⟨_, ev₃⟩
       | if_true =>
         exfalso
         exact (booleans_do_not_eval _) ⟨_, ev₃⟩
     | if_true =>
       cases ev₂ with
       | if_ ev₃ =>
         exfalso
         exact (booleans_do_not_eval _) ⟨_, ev₃⟩
       | if_true => rfl
     | if_false =>
       cases ev₂ with
       | if_ ev₃ =>
         exfalso
         exact (booleans_do_not_eval _) ⟨_, ev₃⟩
       | if_false => rfl

inductive MultiStep : Rel T T where
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

theorem eval_decreases : ∀ {x y}, Eval x y → y.size < x.size := by
  intro x y ev
  induction ev with
  | if_true | if_false => simp; omega
  | is_zero_zero | is_zero_succ => simp
  | succ ev₁ ih => simp; assumption
  | is_zero => simp; assumption
  | pred_zero => simp
  | pred_succ => simp; omega
  | pred => simp; assumption
  | if_ => simp; assumption

theorem termination_of_evaluation : ∀ t : T, ∃ u, is_normal_form u ∧ t ⇒ u := by
  intro t
  if h : is_normal_form t then
    use t
    apply And.intro
    exact h
    exact MultiStep.rfl
  else
    simp at h
    have ⟨ v, h ⟩ := h
    have := eval_decreases h
    have ⟨ u, ⟨ nfu, v_to_u ⟩ ⟩ := termination_of_evaluation v
    have t_to_v := MultiStep.single h
    have t_to_u := MultiStep.trans t_to_v v_to_u
    use u
  termination_by t => t.size
