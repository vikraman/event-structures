import EventStructures.Family.Path
import EventStructures.Family.Trace
import Mathlib.Logic.Function.Basic

/-! # Computations

Asynchronous paths from the empty configuration. -/

variable {L : Type*} (F : ConfFamily L)

open ConfFamily Path Trace

/-- A computation to `c` is an asynchronous path from the empty configuration. -/
def Computation (c : Conf F) : Type _ :=
  Path.Async F (ConfFamily.empty F) c

/-- All computations, paired with their target configuration. -/
def Computations : Type _ := Σ c : Conf F, Computation F c

/-- `t` linearises `c` when some path to `c` has a trace equivalent to `t`. -/
def isLinearisation (c : Conf F) (t : List F.Event) : Prop :=
  ∃ p : Path F (ConfFamily.empty F) c,
    ConfFamily.TraceEquivFrom F (ConfFamily.empty F).val (Path.trace F p) t

/-- Every computation determines a linearisation of its target configuration. -/
lemma computation_is_linearisation {c : Conf F} (comp : Computation F c) :
    ∃ t : List F.Event, isLinearisation F c t := by
  obtain ⟨p, rfl⟩ := Quotient.exists_rep comp
  exact ⟨Path.trace F p, ⟨p, .refl _⟩⟩

/-- Configurations reachable by a computation. -/
def ReachableConf : Type _ := {c : Conf F // Nonempty (Computation F c)}

/-- Every computation targets a reachable configuration. -/
def computation_to_reachable : Computations F → ReachableConf F :=
  fun p => ⟨p.1, ⟨p.2⟩⟩

/-- The map from computations to reachable configurations is surjective. -/
lemma computation_to_reachable_surjective :
    Function.Surjective (computation_to_reachable F) :=
  fun ⟨c, ⟨comp⟩⟩ => ⟨⟨c, comp⟩, rfl⟩
