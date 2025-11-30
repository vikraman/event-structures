import EventStructures.Basic

namespace Trace

variable (es : EventStructure)
open EventStructure
local infixl:50 " ⋈ " => es.concurrent

/-- Trace equivalence:
    two traces are equivalent if one can be obtained from the other
    by swapping adjacent concurrent events. -/
inductive TraceEquiv : List es.Event → List es.Event → Prop
  | refl (t : List es.Event) : TraceEquiv t t
  | swap {e₁ e₂ : es.Event} {t₁ t₂ t₃ : List es.Event} :
      (ind : e₁ ⋈ e₂) →
      TraceEquiv (t₁ ++ e₁ :: e₂ :: t₂) t₃ →
      TraceEquiv (t₁ ++ e₂ :: e₁ :: t₂) t₃

/-- Notation for trace equivalence. -/
local infixr:60 " ≈ₜ " => TraceEquiv es

/-- Trace equivalence is reflexive. -/
lemma traceEquiv_refl : Reflexive (TraceEquiv es) :=
  TraceEquiv.refl

/-- Trace equivalence is transitive. -/
lemma traceEquiv_trans : Transitive (TraceEquiv es) := by
  intro t₁ t₂ t₃ h₁₂ h₂₃
  induction h₁₂ with
  | refl t => exact h₂₃
  | swap ind h ih =>
    exact TraceEquiv.swap ind (ih h₂₃)

/-- Trace equivalence is symmetric. -/
lemma traceEquiv_symm : Symmetric (TraceEquiv es) := by
  intro t₁ t₂ h
  induction h with
  | refl t => exact TraceEquiv.refl t
  | @swap e₁ e₂ t₁' t₂' t₃' ind h ih =>
    -- ih: t₃' ≈ₜ (t₁' ++ e₁ :: e₂ :: t₂')
    -- Goal: t₃' ≈ₜ (t₁' ++ e₂ :: e₁ :: t₂')
    have step : (t₁' ++ e₁ :: e₂ :: t₂') ≈ₜ (t₁' ++ e₂ :: e₁ :: t₂') :=
      TraceEquiv.swap (es.concurrent_symm ind) (TraceEquiv.refl _)
    exact traceEquiv_trans es ih step

/-- Trace equivalence is an equivalence relation. -/
instance : Equivalence (TraceEquiv es) where
  refl := @traceEquiv_refl es
  symm := @traceEquiv_symm es
  trans := @traceEquiv_trans es

/-- Trans instance for calc proofs. -/
instance : Trans (TraceEquiv es) (TraceEquiv es) (TraceEquiv es) where
  trans h₁₂ h₂₃ := traceEquiv_trans es h₁₂ h₂₃

/-- Trace equivalence is a left congruence for append. -/
lemma traceEquiv_append_left {t₁ t₂ : List es.Event} (h : t₁ ≈ₜ t₂) (t : List es.Event) :
    (t ++ t₁) ≈ₜ (t ++ t₂) := by
  induction h generalizing t with
  | refl t => exact TraceEquiv.refl _
  | @swap e₁ e₂ t₁' t₂' t₃' ind h ih =>
    -- h: (t₁' ++ e₁ :: e₂ :: t₂') ≈ₜ t₃'
    -- Goal: (t ++ t₁' ++ e₂ :: e₁ :: t₂') ≈ₜ (t ++ t₃')
    calc (t ++ (t₁' ++ e₂ :: e₁ :: t₂'))
        = ((t ++ t₁') ++ e₂ :: e₁ :: t₂') := by simp [List.append_assoc]
      _ ≈ₜ ((t ++ t₁') ++ e₁ :: e₂ :: t₂') := TraceEquiv.swap ind (TraceEquiv.refl _)
      _ = (t ++ (t₁' ++ e₁ :: e₂ :: t₂')) := by simp [List.append_assoc]
      _ ≈ₜ (t ++ t₃') := ih t

/-- Trace equivalence is a right congruence for append. -/
lemma traceEquiv_append_right {t₁ t₂ : List es.Event} (h : t₁ ≈ₜ t₂) (t : List es.Event) :
    (t₁ ++ t) ≈ₜ (t₂ ++ t) := by
  induction h with
  | refl t => exact TraceEquiv.refl _
  | @swap e₁ e₂ t₁' t₂' t₃' ind h ih =>
    -- h: (t₁' ++ e₁ :: e₂ :: t₂') ≈ₜ t₃'
    -- Goal: (t₁' ++ e₂ :: e₁ :: t₂' ++ t) ≈ₜ (t₃' ++ t)
    calc (t₁' ++ e₂ :: e₁ :: t₂' ++ t)
        = (t₁' ++ e₂ :: e₁ :: (t₂' ++ t)) := by simp [List.append_assoc]
      _ ≈ₜ (t₁' ++ e₁ :: e₂ :: (t₂' ++ t)) := TraceEquiv.swap ind (TraceEquiv.refl _)
      _ = (t₁' ++ e₁ :: e₂ :: t₂' ++ t) := by simp [List.append_assoc]
      _ ≈ₜ (t₃' ++ t) := ih

/-- Trace equivalence is a congruence for append. -/
lemma traceEquiv_append {t₁ t₂ t₃ t₄ : List es.Event}
    (h₁ : t₁ ≈ₜ t₂) (h₂ : t₃ ≈ₜ t₄) : (t₁ ++ t₃) ≈ₜ (t₂ ++ t₄) :=
  traceEquiv_trans es (traceEquiv_append_right es h₁ t₃) (traceEquiv_append_left es h₂ t₂)

end Trace
