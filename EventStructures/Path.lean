import EventStructures.Basic
import EventStructures.Configuration
import Mathlib.CategoryTheory.Category.Basic

variable (es : EventStructure)
open EventStructure
open Configuration

/-- Notation for the enabling relation. -/
local infix:50 " ⊢ " => enables es

/-- An edge in the configuration graph of an event structure:
    from configuration c₁ to configuration c₂ by adding event e. -/
structure Edge where
  c₁ : Conf es
  c₂ : Conf es
  e : es.Event
  c₁_enables : (c₁.val) ⊢ e
  c₂_equals : c₂.val = (c₁.val ∪ {e})

/-- A path in the configuration graph of an event structure. -/
inductive Path : Conf es → Conf es → Type _
  | refl {c : Conf es} : Path c c
  | step {c₁ c₂ c₃ : Conf es} (hEdge : Edge es) (hPath : Path c₂ c₃) : Path c₁ c₃

namespace Path

/-- Identity path. -/
def path_id (c : Conf es) : Path es c c :=
  Path.refl

/-- Composition of paths. -/
def path_comp {c₁ c₂ c₃ : Conf es} (h₁₂ : Path es c₁ c₂) (h₂₃ : Path es c₂ c₃) :
    Path es c₁ c₃ :=
  match h₁₂ with
  | refl => h₂₃
  | step hEdge hPath => Path.step hEdge (path_comp hPath h₂₃)

/-- Left identity law: composing with the identity path on the right. -/
lemma path_comp_id {c₁ c₂ : Conf es} (h : Path es c₁ c₂) :
    path_comp es h (path_id es c₂) = h := by
  induction h with
  | refl => rfl
  | step hEdge hPath ih =>
    simp only [path_comp, path_id] at ih ⊢
    rw [ih]

/-- Right identity law: composing with the identity path on the left. -/
lemma path_id_comp {c₁ c₂ : Conf es} (h : Path es c₁ c₂) :
    path_comp es (path_id es c₁) h = h := rfl

/-- Associativity law: composition of paths is associative. -/
lemma path_comp_assoc {c₁ c₂ c₃ c₄ : Conf es}
    (h₁₂ : Path es c₁ c₂) (h₂₃ : Path es c₂ c₃) (h₃₄ : Path es c₃ c₄) :
    path_comp es (path_comp es h₁₂ h₂₃) h₃₄ = path_comp es h₁₂ (path_comp es h₂₃ h₃₄) := by
  induction h₁₂ with
  | refl => rfl
  | step hEdge hPath ih =>
    simp only [path_comp]
    rw [ih]

end Path

/-- The path category of an event structure. -/
instance : CategoryTheory.Category (Conf es) where
  Hom := Path es
  id := Path.path_id es
  comp := Path.path_comp es
  id_comp := Path.path_id_comp es
  comp_id := Path.path_comp_id es
  assoc := Path.path_comp_assoc es
