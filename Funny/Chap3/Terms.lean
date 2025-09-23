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

inductive IsBool : T → Prop where
  | true : IsBool T.true
  | false : IsBool T.false

def is_bool (t : T) : Prop :=
  t = T.true ∨ t = T.false

theorem IsBool.cases : ∀ {x : T}, IsBool x → x = T.true ∨ x = T.false := by
  intro x is_b
  cases is_b <;> simp

inductive IsNumber : T → Prop where
  | zero : IsNumber T.zero
  | succ : ∀ {n}, {_ : IsNumber n} → IsNumber (T.succ n)

def is_number (t : T) : Prop :=
  t = T.zero ∨ ∃ n, t = T.succ n

theorem IsNumber.cases : ∀ {x : T}, IsNumber x → x = T.zero ∨ ∃n, IsNumber n ∧ x = T.succ n := by
  intro x is_n
  cases is_n <;> simp; assumption

inductive IsValue : T → Prop where
  | bool : ∀ {t}, {_ : IsBool t} → IsValue t
  | number : ∀ {n}, {_ : IsNumber n} → IsValue n

theorem IsValue.cases : ∀ {x : T}, IsValue x →
  (x = T.true ∨ x = T.false) ∨ (x = T.zero ∨ ∃ n : T, IsNumber n ∧ x = T.succ n) := by
  intro x is_value
  cases is_value with
  | @bool is_bool => left; exact is_bool.cases
  | @number is_number => right; exact is_number.cases

open T in
inductive Eval : Rel T T where
  | if_true : ∀ {t₂ t₃}, Eval (if_then_else true t₂ t₃) t₂
  | if_false : ∀ {t₂ t₃}, Eval (if_then_else false t₂ t₃) t₃
  | if_ : ∀ {t₁ t₁' t₂ t₃}, Eval t₁ t₁' → Eval (if_then_else t₁ t₂ t₃) (if_then_else t₁' t₂ t₃)
  | succ : ∀ {t t'}, Eval t t' → Eval (succ t) (succ t')
  | pred_zero : Eval (pred zero) zero
  | pred_succ : ∀ {t}, {_ : IsNumber t} → Eval (pred (succ t)) t
  | pred : ∀ {t t'}, Eval t t' → Eval (pred t) (pred t')
  | is_zero_zero : Eval (is_zero zero) true
  | is_zero_succ : ∀ {t}, {_ : IsNumber t} → Eval (is_zero (succ t)) false
  | is_zero : ∀ {t t'}, Eval t t' → Eval (is_zero t) (is_zero t')

@[simp]
def is_normal_form (x : T) : Prop := ¬∃y : T, Eval x y

@[simp]
def is_stuck (x : T) : Prop := is_normal_form x ∧ ¬IsValue x

theorem succ_is_not_zero : ∀ {t₁ t₂}, Eval (T.succ t₁) t₂ → ¬(t₂ = T.zero) := by
  intro t₁ t₂ ev₁ eq
  rw [eq] at ev₁
  cases ev₁

theorem booleans_do_not_eval : ∀ (x : T), {_ : IsBool x} → is_normal_form x := by
  intro x is_bool ⟨y, ev⟩
  have := is_bool.cases
  cases x with
  | true
  | false => cases ev
  | is_zero
  | pred
  | if_then_else
  | zero
  | succ =>
    simp_all

theorem numbers_do_not_eval : ∀ (x : T), {_ : IsNumber x} → is_normal_form x := by
  intro x is_number ⟨y, ev⟩
  have := is_number.cases
  cases x with
  | true
  | false
  | is_zero
  | pred
  | if_then_else => simp_all
  | zero => cases ev
  | succ m =>
    if h : IsNumber m
    then
      cases ev with
      | succ ev₁ =>
        have := @numbers_do_not_eval m h
        apply this ⟨ _, ev₁ ⟩
    else
      simp_all

theorem value_implies_bool_or_number : ∀ x, IsValue x → IsBool x ∨ IsNumber x := by
  intro x is_value
  cases is_value with
  | @bool x => left; assumption
  | @number x => right; assumption

theorem values_do_not_eval : ∀ (x : T), {_ : IsValue x} → is_normal_form x := by
  intro x is_value
  have := is_value.cases
  if h₁ : IsNumber x then
    exact @numbers_do_not_eval x h₁
  else if h₂ : IsBool x then
    exact @booleans_do_not_eval x h₂
  else
    have := value_implies_bool_or_number x is_value
    cases this with
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
         have := @IsNumber.succ t'' is_number
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
         have := @IsNumber.succ _ is_number
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
         have := @IsNumber.zero
         have := @numbers_do_not_eval _ this
         exfalso
         exact this ⟨_, ev₃⟩
     | @is_zero_succ _ is_number =>
       cases ev₂ with
       | is_zero ev₃ =>
         have := @IsNumber.succ _ is_number
         exfalso
         exact @numbers_do_not_eval _ this ⟨_, ev₃⟩
       | is_zero_succ => rfl
     | is_zero ev₃ =>
       cases ev₂ with
       | is_zero ev₄ =>
         have := determinancy_of_one_step ev₃ ev₄
         rw [this]
       | @is_zero_succ _ is_number =>
         have := @IsNumber.succ _ is_number
         exfalso
         exact @numbers_do_not_eval _ this ⟨_, ev₃⟩
       | is_zero_zero =>
         have := @IsNumber.zero
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
         have := @IsBool.false
         exfalso
         exact @booleans_do_not_eval _ this ⟨_, ev₃⟩
       | if_true =>
         have := @IsBool.true
         exfalso
         exact @booleans_do_not_eval _ this ⟨_, ev₃⟩
     | if_true =>
       cases ev₂ with
       | if_ ev₃ =>
         have := @IsBool.true
         exfalso
         exact @booleans_do_not_eval _ this ⟨_, ev₃⟩
       | if_true => rfl
     | if_false =>
       cases ev₂ with
       | if_ ev₃ =>
         have := @IsBool.false
         exfalso
         exact @booleans_do_not_eval _ this ⟨_, ev₃⟩
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

-- theorem uniqueness_of_normal_forms : ∀ t u u', is_normal_form u → is_normal_form u' → t ⇒ u → t ⇒ u' → u = u' := by
--   intro t u u' nfu nfu' mse mse'
--   induction mse with
--   | rfl =>
--     cases mse' with
--     | rfl => rfl
--     | single ev =>
--       simp at nfu
--       exfalso
--       exact nfu u' ev
--     | trans h₁ h₂ =>
--       have x_eq_y := normal_form_only_eval_to_itself _ _ nfu h₁
--       rw [x_eq_y] at nfu
--       have y_eq_u := normal_form_only_eval_to_itself _ u' nfu h₂
--       rw [x_eq_y, y_eq_u]
--   | single ev =>
--     cases mse' with
--     | rfl =>
--       simp at nfu'
--       exfalso
--       exact nfu' _ ev
--     | single ev₁ =>
--       exact determinancy_of_one_step ev ev₁
--     | trans h₁ h₂ =>
--       have x_ev_y := MultiStep.single ev
--       have x_ev_u' := MultiStep.trans h₁ h₂
--       have y_ev_u' := helper x_ev_u' x_ev_y nfu'
--       exact helper₂ _ u' nfu y_ev_u'

--   | trans h₁ h₂ ih₁ ih₂ =>
--     cases mse' with
--     | rfl =>
--       have u'_eq_y := normal_form_only_eval_to_itself u' _ nfu' h₁
--       rw [u'_eq_y] at ih₂
--       have  z_eq_y := ih₂ nfu MultiStep.rfl u_value
--       rw [z_eq_y, u'_eq_y]
--     | single ev₁ =>
--       have x_ev_u' := MultiStep.single ev₁
--       suffices ∀ {x y z}, x ⇒ y → x ⇒ z → is_normal_form y → z ⇒ y by
--         have y_ev_u' := this x_ev_u' h₁ nfu'
--         exact ih₂ nfu y_ev_u' u_value
--       exact helper
--     | trans h₃ h₄ =>
--       have x_ev_u' := MultiStep.trans h₃ h₄
--       have y_ev_u' := helper x_ev_u' h₁ nfu'
--       exact ih₂ nfu y_ev_u' u_value
