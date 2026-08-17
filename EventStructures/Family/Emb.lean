import EventStructures.Family.Basic
import Mathlib.Logic.Function.Basic

/-! # Embeddings of configuration families

An embedding needs only injectivity and reflection of configurations; the order
and conflict conditions of the prime setting are what *prove* reflection there. -/

namespace ConfFamily

variable {L : Type*} {E F : ConfFamily L}

/-- An injective map whose preimage sends configurations to configurations. -/
structure Emb (E F : ConfFamily L) where
  f : E.Event → F.Event
  inj : Function.Injective f
  config_restrict : ∀ {c : Set F.Event}, F.Config c → E.Config {y | f y ∈ c}

namespace Emb

variable (ι : Emb E F)

lemma finite {c : Set F.Event} (h : c.Finite) : {y | ι.f y ∈ c}.Finite :=
  h.preimage ι.inj.injOn

/-- Restricting along an embedding commutes with adding one event. -/
lemma preimage_insert (c : Set F.Event) (x : E.Event) :
    {y | ι.f y ∈ c ∪ {ι.f x}} = {y | ι.f y ∈ c} ∪ {x} := by
  ext y
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (ι.inj h)
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (congrArg ι.f h)

lemma enables_restrict {c : Set F.Event} {x : E.Event} (h : F.enables c (ι.f x)) :
    E.enables {y | ι.f y ∈ c} x := by
  refine ⟨ι.config_restrict h.1, ?_⟩
  have hx := ι.config_restrict h.2
  rwa [ι.preimage_insert] at hx

end Emb

end ConfFamily
