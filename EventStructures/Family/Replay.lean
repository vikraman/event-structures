import EventStructures.Family.Log

/-! # Replay

Least and greatest computations compatible with a log. These are defined
only on the family of configurations. -/

open ConfFamily

variable {L : Type*} (F : ConfFamily L) (R : F.Event → F.Event → Prop)

namespace Replay

local infixl:50 " ⊨ " => Log.compatibleWithLog F R

/-- The target configuration of a computation. -/
def conf (σ : Computations F) : Conf F := σ.1

/-- A least replay of `l`: compatible, and contained in every compatible computation. -/
@[simp]
def isMinReplay (l : Set F.Event) (σ : Computations F) : Prop :=
  σ ⊨ l ∧ ∀ σ' : Computations F, σ' ⊨ l → (conf F σ).1 ⊆ (conf F σ').1

/-- A greatest replay of `l`. -/
@[simp]
def isMaxReplay (l : Set F.Event) (σ : Computations F) : Prop :=
  σ ⊨ l ∧ ∀ σ' : Computations F, σ' ⊨ l → (conf F σ').1 ⊆ (conf F σ).1

lemma minReplay_unique_config {l : Set F.Event} {σ₁ σ₂ : Computations F}
    (h₁ : isMinReplay F R l σ₁) (h₂ : isMinReplay F R l σ₂) :
    (conf F σ₁).1 = (conf F σ₂).1 :=
  Set.Subset.antisymm (h₁.2 σ₂ h₂.1) (h₂.2 σ₁ h₁.1)

lemma maxReplay_unique_config {l : Set F.Event} {σ₁ σ₂ : Computations F}
    (h₁ : isMaxReplay F R l σ₁) (h₂ : isMaxReplay F R l σ₂) :
    (conf F σ₁).1 = (conf F σ₂).1 :=
  Set.Subset.antisymm (h₂.2 σ₁ h₁.1) (h₁.2 σ₂ h₂.1)

lemma minReplay_unique {l : Set F.Event} {σ₁ σ₂ : Computations F}
    (h₁ : isMinReplay F R l σ₁) (h₂ : isMinReplay F R l σ₂) :
    conf F σ₁ = conf F σ₂ :=
  Subtype.ext (minReplay_unique_config F R h₁ h₂)

lemma maxReplay_unique {l : Set F.Event} {σ₁ σ₂ : Computations F}
    (h₁ : isMaxReplay F R l σ₁) (h₂ : isMaxReplay F R l σ₂) :
    conf F σ₁ = conf F σ₂ :=
  Subtype.ext (maxReplay_unique_config F R h₁ h₂)

/-- Two computations are label-equivalent if their configurations have the same labels. -/
def LabelEquivComputation (σ₁ σ₂ : Computations F) : Prop :=
  F.label '' (conf F σ₁).1 = F.label '' (conf F σ₂).1

/-- A least replay measured by labels rather than events. -/
@[simp]
def isMinLabelReplay (l : Set F.Event) (σ : Computations F) : Prop :=
  σ ⊨ l ∧ ∀ σ' : Computations F, σ' ⊨ l →
    F.label '' (conf F σ).1 ⊆ F.label '' (conf F σ').1

/-- A least replay is least on labels too. -/
lemma isMinReplay_imp_isMinLabelReplay {l : Set F.Event} {σ : Computations F}
    (h : isMinReplay F R l σ) : isMinLabelReplay F R l σ :=
  ⟨h.1, fun σ' hσ' => Set.image_mono (h.2 σ' hσ')⟩

end Replay
