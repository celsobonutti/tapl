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

-- inductive T : Type where
--   | true : T
--   | false : T
--   | if_then_else : T → T → T → T
--   | zero : T
--   | succ : T → T
--   | pred : T → T
--   | is_zero : T → T
--   deriving DecidableEq, Ord

inductive IsBool : T → Prop where
  | true : IsBool T.true
  | false : IsBool T.false

theorem IsBool.cases : ∀ {x : T}, IsBool x → x = T.true ∨ x = T.false := by
  intro x is_b
  cases is_b <;> simp

inductive IsNumber : T → Prop where
  | zero : IsNumber T.zero
  | succ : ∀ {n}, {_ : IsNumber n} → IsNumber (T.succ n)

theorem IsNumber.cases : ∀ {x : T}, IsNumber x → x = T.zero ∨ ∃n, IsNumber n ∧ x = T.succ n := by
  intro x is_n
  cases is_n <;> simp; assumption

inductive IsValue : T → Prop where
  | bool : ∀ {t}, {_ : IsBool t} → IsValue t
  | number : ∀ {n}, {_ : IsNumber n} → IsValue n

open T in
inductive Eval : Rel T T where
  | if_true : ∀ {t₂ t₃}, Eval (if_then_else true t₂ t₃) t₂
  | if_false : ∀ {t₂ t₃}, Eval (if_then_else false t₂ t₃) t₃
  | if : ∀ {t₁ t₁' t₂ t₃}, Eval t₁ t₁' → Eval (if_then_else t₁ t₂ t₃) (if_then_else t₁' t₂ t₃)
  | succ : ∀ {t t'}, Eval t t' → Eval (succ t) (succ t')
  | pred_zero : Eval (pred zero) zero
  | pred_succ : ∀ {t}, {_ : IsNumber t} → Eval (pred (succ t)) t
  | pred : ∀ {t t'}, Eval t t' → Eval (pred t) (pred t')
  | is_zero_zero : Eval (is_zero zero) true
  | is_zero_succ : ∀ {t}, {_ : IsNumber t} → Eval (is_zero (succ t)) false
  | is_zero : ∀ {t t'}, Eval t t' → Eval t t' → Eval (is_zero t) (is_zero t')
