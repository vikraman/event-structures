import EventStructures.Basic
import EventStructures.Configuration
import EventStructures.Trace
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Data.Setoid.Basic

variable (es : EventStructure)
open EventStructure
open Configuration

/-- Notation for the enabling relation. -/
local infix:50 " ⊢ " => enables es

/-- An edge in the configuration graph of an event structure:
    from configuration c₁ to configuration c₂ by adding event e. -/
structure Edge where
  conf₁ : Conf es
  conf₂ : Conf es
  event : es.Event
  conf₁_enables : (conf₁.val) ⊢ event
  conf₂_equals : conf₂.val = (conf₁.val ∪ {event})

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

/-- Trace of the path -/
def trace {c₁ c₂ : Conf es} (hPath : Path es c₁ c₂) : List es.Event :=
  match hPath with
  | refl => []
  | step hEdge hPath' => hEdge.event :: trace hPath'

/-- Notation for trace equivalence. -/
local infixr:60 " ≈ₜ " => TraceEquiv es

/-- Path equivalence is the kernel of the trace function. -/
instance pathSetoid (c₁ c₂ : Conf es) : Setoid (Path es c₁ c₂) :=
  Setoid.ker (trace es)

/-- Two paths are equivalent if their traces are trace equivalent -/
def PathEquiv {c₁ c₂ : Conf es} (p₁ p₂ : Path es c₁ c₂) : Prop :=
  (pathSetoid es c₁ c₂).r p₁ p₂

/-- Notation for path equivalence. -/
local infixr:60 " ≈ₚ " => PathEquiv es

/-- Path equivalence is reflexive. -/
lemma pathEquiv_refl {c₁ c₂ : Conf es} : Reflexive (@PathEquiv es c₁ c₂) :=
  (pathSetoid es c₁ c₂).iseqv.refl

/-- Path equivalence is symmetric. -/
lemma pathEquiv_symm {c₁ c₂ : Conf es} : Symmetric (@PathEquiv es c₁ c₂) :=
  fun _ _ => (pathSetoid es c₁ c₂).iseqv.symm

/-- Path equivalence is transitive. -/
lemma pathEquiv_trans {c₁ c₂ : Conf es} : Transitive (@PathEquiv es c₁ c₂) :=
  fun _ _ _ => (pathSetoid es c₁ c₂).iseqv.trans

/-- Path equivalence is an equivalence relation. -/
instance pathEquivEquivalence (c₁ c₂ : Conf es) : Equivalence (@PathEquiv es c₁ c₂) where
  refl := pathEquiv_refl es
  symm := @pathEquiv_symm es c₁ c₂
  trans := @pathEquiv_trans es c₁ c₂

/-- Trace of path composition is concatenation of traces. -/
lemma trace_comp {c₁ c₂ c₃ : Conf es} (p₁₂ : Path es c₁ c₂) (p₂₃ : Path es c₂ c₃) :
    trace es (path_comp es p₁₂ p₂₃) = trace es p₁₂ ++ trace es p₂₃ := by
  induction p₁₂ with
  | refl => rfl
  | step hEdge hPath ih =>
    simp only [path_comp, trace, ih]
    rw [List.cons_append]

/-- Asynchronous path: paths quotiented by path equivalence. -/
def Async (c₁ c₂ : Conf es) : Type _ :=
  Quotient (pathSetoid es c₁ c₂)

namespace Async

/-- Lift a path to an asynchronous path. -/
def mk {c₁ c₂ : Conf es} (p : Path es c₁ c₂) : Async es c₁ c₂ :=
  Quotient.mk (pathSetoid es c₁ c₂) p

/-- Identity asynchronous path. -/
def async_path_id (c : Conf es) : Async es c c :=
  mk es (Path.path_id es c)

/-- Composition of asynchronous paths. -/
def async_path_comp {c₁ c₂ c₃ : Conf es}
    (p₁₂ : Async es c₁ c₂) (p₂₃ : Async es c₂ c₃) : Async es c₁ c₃ :=
  Quotient.lift₂
    (fun p₁₂ p₂₃ => mk es (Path.path_comp es p₁₂ p₂₃))
    (fun a₁ b₁ a₂ b₂ ha hb => Quotient.sound <| by
      calc Path.trace es (Path.path_comp es a₁ b₁)
          = Path.trace es a₁ ++ Path.trace es b₁ := Path.trace_comp es a₁ b₁
        _ = Path.trace es a₂ ++ Path.trace es b₂ := by rw [ha, hb]
        _ = Path.trace es (Path.path_comp es a₂ b₂) := (Path.trace_comp es a₂ b₂).symm)
    p₁₂ p₂₃

/-- Left identity law for asynchronous path composition. -/
lemma async_path_id_comp {c₁ c₂ : Conf es} (p : Async es c₁ c₂) :
    async_path_comp es (async_path_id es c₁) p = p := by
  induction p using Quotient.ind
  rfl

/-- Right identity law for asynchronous path composition. -/
lemma async_path_comp_id {c₁ c₂ : Conf es} (p : Async es c₁ c₂) :
    async_path_comp es p (async_path_id es c₂) = p := by
  induction p using Quotient.ind
  unfold async_path_comp async_path_id mk Path.path_id
  simp only [Quotient.lift₂_mk]
  congr 1
  exact Path.path_comp_id es _

/-- Associativity law for asynchronous path composition. -/
lemma assoc {c₁ c₂ c₃ c₄ : Conf es}
    (p₁₂ : Async es c₁ c₂) (p₂₃ : Async es c₂ c₃) (p₃₄ : Async es c₃ c₄) :
    async_path_comp es (async_path_comp es p₁₂ p₂₃) p₃₄ =
    async_path_comp es p₁₂ (async_path_comp es p₂₃ p₃₄) := by
  induction p₁₂ using Quotient.ind
  induction p₂₃ using Quotient.ind
  induction p₃₄ using Quotient.ind
  simp only [async_path_comp, Quotient.lift₂_mk]
  apply Quotient.sound
  rw [Path.path_comp_assoc]

end Async

end Path

/-- The path category of an event structure. -/
instance pathCategory : CategoryTheory.Category (Conf es) where
  Hom := Path es
  id := Path.path_id es
  comp := Path.path_comp es
  id_comp := Path.path_id_comp es
  comp_id := Path.path_comp_id es
  assoc := Path.path_comp_assoc es

/-- The asynchronous path category of an event structure. -/
instance asyncPathCategory : CategoryTheory.Category (Conf es) where
  Hom := Path.Async es
  id := Path.Async.async_path_id es
  comp := Path.Async.async_path_comp es
  id_comp := Path.Async.async_path_id_comp es
  comp_id := Path.Async.async_path_comp_id es
  assoc := Path.Async.assoc es
