import EventStructures.Prime.Basic
import EventStructures.Family.Trace

/-! # Traces of a prime event structure

Independence is concurrency: consistent and causally unordered. -/

variable {L : Type*} (P : PES L)

namespace PES

local infixl:50 " ⋈ " => P.concurrent
local infixr:60 " ≈ₜ " => TraceEquiv P.concurrent

/-- A labelling is concurrency-respecting if it gives concurrent events equal labels. -/
abbrev ConcurrencyRespecting : Prop := Trace.LabelRespecting P.concurrent P.label

/-- Setoid of traces of a prime event structure. -/
instance traceSetoid : Setoid (List P.Event) :=
  Trace.traceEquivSetoid P.concurrent P.concurrent_symm

/-- The trace monoid: lists of events quotiented by trace equivalence. -/
def TraceMonoid : Type := Quotient (traceSetoid P)

namespace Monoid

/-- Lift a list to the trace monoid. -/
def mk (t : List P.Event) : TraceMonoid P := Quotient.mk (traceSetoid P) t

/-- Multiplication in the trace monoid (concatenation of traces). -/
instance : Mul (TraceMonoid P) where
  mul := Quotient.lift₂ (fun t₁ t₂ => mk P (t₁ ++ t₂))
    (fun _ _ _ _ h₁ h₂ => Quotient.sound (Trace.traceEquiv_append P.concurrent h₁ h₂))

/-- Identity element in the trace monoid (empty trace). -/
instance : One (TraceMonoid P) where
  one := mk P []

/-- Left identity law for trace monoid. -/
lemma one_mul (x : TraceMonoid P) : 1 * x = x := by
  obtain ⟨t, rfl⟩ := Quotient.exists_rep x
  change mk P ([] ++ t) = mk P t
  simp

/-- Right identity law for trace monoid. -/
lemma mul_one (x : TraceMonoid P) : x * 1 = x := by
  obtain ⟨t, rfl⟩ := Quotient.exists_rep x
  change mk P (t ++ []) = mk P t
  simp

/-- Associativity law for trace monoid. -/
lemma mul_assoc (x y z : TraceMonoid P) : (x * y) * z = x * (y * z) := by
  obtain ⟨t₁, rfl⟩ := Quotient.exists_rep x
  obtain ⟨t₂, rfl⟩ := Quotient.exists_rep y
  obtain ⟨t₃, rfl⟩ := Quotient.exists_rep z
  change mk P ((t₁ ++ t₂) ++ t₃) = mk P (t₁ ++ (t₂ ++ t₃))
  simp

/-- The trace monoid is a monoid. -/
instance : Monoid (TraceMonoid P) where
  mul_assoc := mul_assoc P
  one_mul := one_mul P
  mul_one := mul_one P

/-- If the concurrency relation is full, the head of the list can be moved to the end -/
lemma move_head_full
    (hfull : ∀ e₁ e₂ : P.Event, e₁ ⋈ e₂) :
    ∀ (e : P.Event) (t : List P.Event),
    TraceEquiv P.concurrent (e :: t) (t ++ [e]) := by
  intro e t
  induction t with
  | nil => exact TraceEquiv.refl _
  | cons e' t' ih =>
    calc (e :: e' :: t')
      _ = ([] ++ e :: e' :: t') := by simp
      _ ≈ₜ ([] ++ e' :: e :: t') := TraceEquiv.swap (hfull e' e) (TraceEquiv.refl _)
      _ = (e' :: e :: t') := by simp
      _ ≈ₜ (e' :: (t' ++ [e])) := Trace.traceEquiv_append_left P.concurrent ih [e']
      _ = ((e' :: t') ++ [e]) := by simp

/-- If the concurrency relation is full, the monoid is commutative. -/
lemma mul_comm_full
    (hfull : ∀ e₁ e₂ : P.Event, e₁ ⋈ e₂)
    : ∀ t₁ t₂ : List P.Event, TraceEquiv P.concurrent (t₁ ++ t₂) (t₂ ++ t₁) := by
  intro t₁
  induction t₁ with
  | nil =>
    intro t₂
    calc ([] ++ t₂)
        = t₂ := List.nil_append t₂
      _ ≈ₜ t₂ := TraceEquiv.refl _
      _ = (t₂ ++ []) := (List.append_nil t₂).symm
  | cons e t₁' ih =>
    intro t₂
    calc ((e :: t₁') ++ t₂)
      _ = (e :: (t₁' ++ t₂)) := by simp
      _ ≈ₜ (e :: (t₂ ++ t₁')) := Trace.traceEquiv_append_left P.concurrent (ih t₂) [e]
      _ = ((e :: t₂) ++ t₁') := by simp
      _ ≈ₜ (t₂ ++ [e] ++ t₁') :=
            Trace.traceEquiv_append_right P.concurrent (move_head_full P hfull e t₂) t₁'
      _ = (t₂ ++ ([e] ++ t₁')) := by simp

/-- If the concurrency relation is empty, trace equivalence is just list equality. -/
lemma traceEquiv_eq_empty
    (hempty : ∀ e₁ e₂ : P.Event, ¬ e₁ ⋈ e₂)
    {t₁ t₂ : List P.Event} (h : TraceEquiv P.concurrent t₁ t₂) : t₁ = t₂ := by
  induction h with
  | refl t => rfl
  | @swap e₁ e₂ a b c ind hprev ih =>
    exact False.elim ((hempty e₁ e₂) ind)

/-- If the concurrency relation is empty and there are at least two distinct events,
    then the monoid is not commutative. -/
lemma mul_not_comm_empty
    (hempty : ∀ e₁ e₂ : P.Event, ¬ e₁ ⋈ e₂)
    (hdistinct : ∃ e₁ e₂ : P.Event, e₁ ≠ e₂) :
    ∃ t₁ t₂ : List P.Event, ¬ TraceEquiv P.concurrent (t₁ ++ t₂) (t₂ ++ t₁) := by
  obtain ⟨e₁, e₂, hneq⟩ := hdistinct
  refine ⟨[e₁], [e₂], ?_⟩
  intro hteq
  have h' : TraceEquiv P.concurrent [e₁, e₂] [e₂, e₁] := by simpa using hteq
  have hlists_eq : [e₁, e₂] = [e₂, e₁] := traceEquiv_eq_empty P hempty h'
  exact hneq (by injection hlists_eq)

end Monoid

end PES

