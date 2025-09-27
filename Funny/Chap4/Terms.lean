import Funny.Chap3.Terms

@[simp]
def is_numerical : T → Bool
  | T.zero => true
  | T.succ m => is_numerical m
  | _ => false

example : ∀ t, is_number t → is_numerical t = true := by
  intro t t_number
  induction t <;> simp_all

@[simp]
def is_val : T → Bool
  | T.true => true
  | T.false => true
  | t => is_numerical t

inductive Exception : Type
  | NoRuleApplies

open Exception

instance {ε : Type} : Coe T (Except ε T) where
  coe := Except.ok

@[simp]
def T.eval_1 : T → Except Exception T
  | T.if_then_else T.true t₁ _ => t₁
  | T.if_then_else T.false _ t₂ => t₂
  | T.if_then_else t₁ t₂ t₃ => do T.if_then_else (←t₁.eval_1) t₂ t₃
  | T.succ t₁ => do T.succ (←t₁.eval_1)
  | T.pred T.zero => T.zero
  | T.pred (T.succ m) =>
    if is_numerical m then
      m
    else do
      T.pred (←(T.succ m).eval_1)
  | T.pred t₁ => do T.pred (←t₁.eval_1)
  | T.is_zero T.zero => T.true
  | T.is_zero (T.succ m) =>
    if is_numerical m then
      T.true
    else do
      T.is_zero (←(T.succ m).eval_1)
  | T.is_zero t₁ => do T.pred (←t₁.eval_1)
  | _ => throw NoRuleApplies

partial def bad_eval (t : T) : T :=
  match t.eval_1 with
    | Except.ok t' => bad_eval t'
    | Except.error _ => t

open T in
def T.eval (t : T) : T :=
  if is_val t then
    t
  else
    match t with
    | if_then_else true t₂ _ => t₂.eval
    | if_then_else false _ t₃ => t₃.eval
    | succ m =>
      if is_numerical m.eval then
        succ m.eval
      else
        t
    | pred zero => zero
    | pred (succ m) =>
      if is_numerical m.eval then
        m.eval
      else
        t
    | pred x => pred x.eval
    | is_zero zero => true
    | is_zero (succ m) =>
      if is_numerical m.eval then
        false
      else
        t
    | _ => t
