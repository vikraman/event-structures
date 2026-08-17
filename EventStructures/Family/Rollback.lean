import EventStructures.Family.Basic
import EventStructures.Family.Reachability

/-! # Rollback

A rollback is a maximal subconfiguration omitting an event. Existence and
uniqueness need coherence; maximality is stated for any family. -/

open ConfFamily

variable {L : Type*} (F : ConfFamily L)

namespace Rollback

/-- A rollback of `e` on `c` is a maximal configuration `m` with `m ⊆ c` and
`e ∉ m`. -/
def isRollback (c : Conf F) (e : F.Event) (m : Conf F) : Prop :=
  m.1 ⊆ c.1 ∧ e ∉ m.1 ∧
  ∀ m' : Conf F, m'.1 ⊆ c.1 → e ∉ m'.1 → m.1 ⊆ m'.1 → m'.1 ⊆ m.1

/-- The set of all rollbacks of event `e` on configuration `c`. -/
def Rollbacks (c : Conf F) (e : F.Event) : Set (Conf F) :=
  {m | isRollback F c e m}

/-- Candidate configurations for rollback. -/
def RollbackCandidates (c : Conf F) (e : F.Event) : Set (Conf F) :=
  {m | m.1 ⊆ c.1 ∧ e ∉ m.1}

@[simp] lemma rollback_subset {c : Conf F} {e : F.Event} {m : Conf F}
    (h : isRollback F c e m) : m.1 ⊆ c.1 :=
  h.1

@[simp] lemma rollback_not_mem {c : Conf F} {e : F.Event} {m : Conf F}
    (h : isRollback F c e m) : e ∉ m.1 :=
  h.2.1

lemma rollback_maximal {c : Conf F} {e : F.Event} {m : Conf F}
    (h : isRollback F c e m) :
    ∀ m' : Conf F, m'.1 ⊆ c.1 → e ∉ m'.1 → m.1 ⊆ m'.1 → m'.1 ⊆ m.1 :=
  h.2.2

lemma isRollback_iff_maximal {c : Conf F} {e : F.Event} {m : Conf F} :
    isRollback F c e m ↔ m ∈ RollbackCandidates F c e ∧
      ∀ m' : Conf F, m' ∈ RollbackCandidates F c e → m.1 ⊆ m'.1 → m'.1 ⊆ m.1 := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · exact ⟨h.1, h.2.1⟩
    · intro m' hm' hsubset
      rcases hm' with ⟨hm'sub, hm'not⟩
      exact h.2.2 m' hm'sub hm'not hsubset
  · intro h
    rcases h with ⟨hm, hmax⟩
    rcases hm with ⟨hmsub, hmnot⟩
    refine ⟨hmsub, hmnot, ?_⟩
    intro m' hm'sub hm'not hsubset
    exact hmax m' ⟨hm'sub, hm'not⟩ hsubset

/-- The union of all subconfigurations of `c` omitting `e`. -/
def rollbackSet (c : Conf F) (e : F.Event) : Set F.Event :=
  ⋃₀ {m | F.Config m ∧ m ⊆ c.val ∧ e ∉ m}

lemma rollbackSet_subset (c : Conf F) (e : F.Event) : rollbackSet F c e ⊆ c.val := by
  rintro x ⟨m, ⟨-, hmc, -⟩, hxm⟩
  exact hmc hxm

lemma rollbackSet_not_mem (c : Conf F) (e : F.Event) : e ∉ rollbackSet F c e := by
  rintro ⟨m, ⟨-, -, hem⟩, hem'⟩
  exact hem hem'

lemma subset_rollbackSet {c m : Conf F} {e : F.Event}
    (hmc : m.val ⊆ c.val) (hem : e ∉ m.val) : m.val ⊆ rollbackSet F c e :=
  fun _ hx => ⟨m.val, ⟨m.2, hmc, hem⟩, hx⟩

end Rollback
