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

end Trace
