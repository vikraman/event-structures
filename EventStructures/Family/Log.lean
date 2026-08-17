import EventStructures.Family.Computation

/-! # Logs

A log records the choice points of a computation. Compatibility is parametric in
the incompatibility relation `R`. -/

open ConfFamily

variable {L : Type*} (F : ConfFamily L) (R : F.Event → F.Event → Prop)

namespace Log

/-- A computation is compatible with a log `l` when `l` is contained in it, its
events are compatible with `l`, and every incompatible event it performs is in
`l`. -/
@[simp]
def compatibleWithLog (σ : Computations F) (l : Set F.Event) : Prop :=
  (∀ e ∈ l, e ∈ σ.1.1) ∧
  (∀ e ∈ σ.1.1, ∀ e' ∈ l, ¬ R e e') ∧
  (∀ e ∈ σ.1.1, ∀ e' : F.Event, R e e' → e ∈ l)

/-- Notation for computation compatible with log. -/
local infixl:50 " ⊨ " => compatibleWithLog F R

lemma compatibleWithLog_log_subset {σ : Computations F} {l : Set F.Event}
    (h : σ ⊨ l) : l ⊆ σ.1.1 := h.1

lemma compatibleWithLog_consistent {σ : Computations F} {l : Set F.Event}
    (h : σ ⊨ l) {e e' : F.Event} (he : e ∈ σ.1.1) (he' : e' ∈ l) : ¬ R e e' :=
  h.2.1 e he e' he'

lemma compatibleWithLog_conflict_in_log {σ : Computations F} {l : Set F.Event}
    (h : σ ⊨ l) {e e' : F.Event} (he : e ∈ σ.1.1) (hconf : R e e') : e ∈ l :=
  h.2.2 e he e' hconf

/-- Computations compatible with a given log. -/
def CompatibleComputations (l : Set F.Event) : Type _ :=
  {σ : Computations F // σ ⊨ l}

/-- The underlying computation. -/
def CompatibleComputations.val {l : Set F.Event} (σ : CompatibleComputations F R l) :
    Computations F := σ.1

/-- The compatibility proof. -/
theorem CompatibleComputations.compatible {l : Set F.Event}
    (σ : CompatibleComputations F R l) : CompatibleComputations.val F R σ ⊨ l := σ.2

/-- The label image of a log. -/
@[simp] def labelLog (l : Set F.Event) : Set L := F.label '' l

lemma label_mem_labelLog {l : Set F.Event} {e : F.Event} (h : e ∈ l) :
    F.label e ∈ labelLog F l := ⟨e, h, rfl⟩

end Log
