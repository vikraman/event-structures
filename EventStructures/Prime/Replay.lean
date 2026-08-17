import EventStructures.Prime.Configuration
import EventStructures.Prime.Log
import EventStructures.Family.Replay
import EventStructures.Stable.Replay

/-! # Replay for a prime event structure

The least/greatest replay *sets* are built from the causal order
and minimal conflict. -/

variable {L : Type*} (es : PES L)
open PES
open Configuration
open Log

/-- Notation for compatibility with a log. -/
local infixl:50 " ⊨ " => PES.compatibleWithLog es

namespace Replay

/-- The downset (or principal ideal) of an event e: all predecessors including e. -/
def downset (e : es.Event) : Set es.Event :=
  {x | x ≤ e}

/-- Notation for minimal conflict. -/
local infixl:50 " ## " => es.minimalConflict

/-- Notation for conflict. -/
local infixl:50 " # " => es.conflict

/-- The minimum replay set of a log l: union of all downsets of events in l. -/
def minReplaySet (l : Set es.Event) : Set es.Event :=
  ⋃ e ∈ l, downset es e

/-- The maximum replay set of a log `l`: the minimum replay set together with
the events forced by a minimal conflict in `l`. -/
def maxReplaySet (l : Set es.Event) : Set es.Event :=
  minReplaySet es l ∪ {e : es.Event | ∀ e₁ e₂ : es.Event, e₁ ## e₂ ∧ e₁ ≤ e → e₁ ∈ l}

/-- The downset is closed under taking predecessors. -/
lemma downset_closed {e x y : es.Event} (hxy : x ≤ y) (hy : y ∈ downset es e) :
    x ∈ downset es e :=
  le_trans hxy hy

/-- The minimum replay set contains the log. -/
lemma minReplaySet_contains_log {l : Set es.Event} : l ⊆ minReplaySet es l := by
  intro e he
  simp only [minReplaySet, downset, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
  exact ⟨e, he, le_rfl⟩

/-- The minimum replay set is closed under predecessors. -/
lemma minReplaySet_closed {l : Set es.Event} {x y : es.Event}
    (hy : y ≤ x) (hx : x ∈ minReplaySet es l) : y ∈ minReplaySet es l := by
  simp only [minReplaySet, downset, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop] at hx ⊢
  obtain ⟨e, he, hxe⟩ := hx
  exact ⟨e, he, le_trans hy hxe⟩

/-- The maximum replay set contains the minimum replay set. -/
lemma minReplaySet_subset_maxReplaySet {l : Set es.Event} :
    minReplaySet es l ⊆ maxReplaySet es l :=
  Set.subset_union_left

/-- Below an event of a conflict-free log, every event is compatible with the
log. -/
lemma downset_compatible_with_log {l : Set es.Event} {e x : es.Event}
    (he : e ∈ l) (hxe : x ≤ e)
    (hl_conflict_free : ∀ {e₁ e₂}, e₁ ∈ l → e₂ ∈ l → ¬(e₁ # e₂)) :
    ∀ e' ∈ l, ¬(x # e') := by
  intro e' he' hconf
  have hconf_symm := es.conflict_symm.symm _ _ hconf
  have : e' # e := es.conflict_hereditary hconf_symm hxe
  have : e # e' := es.conflict_symm.symm _ _ this
  exact hl_conflict_free he he' this

/-- The minimum replay set is compatible with the log. -/
lemma minReplaySet_compatible_with_log {l : Set es.Event}
    (hl_conflict_free : ∀ {e₁ e₂}, e₁ ∈ l → e₂ ∈ l → ¬(e₁ # e₂)) :
    ∀ x ∈ minReplaySet es l, ∀ e ∈ l, ¬(x # e) := by
  intro x hx e he
  simp only [minReplaySet, downset, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop] at hx
  obtain ⟨e', he', hxe'⟩ := hx
  exact downset_compatible_with_log es he' hxe' hl_conflict_free e he

/-- A computation reaching `minReplaySet` is a minimal replay. -/
lemma minReplaySet_is_minimal_replay {l : Set es.Event} {σ : Computations es.toFamily}
    (h_conf : (Replay.conf es.toFamily σ).1 = minReplaySet es l)
    (h_compat : σ ⊨ l) :
    Replay.isMinReplay es.toFamily es.conflict l σ := by
  constructor
  · exact h_compat
  · intro σ' h'_compat
    rw [h_conf]
    intro x hx
    obtain ⟨e, he, hxe⟩ := Set.mem_iUnion₂.mp hx
    -- x ≤ e and e ∈ l
    -- σ' ⊨ l means all events in l are in σ'
    have : e ∈ (Replay.conf es.toFamily σ').1 := h'_compat.1 e he
    exact (Replay.conf es.toFamily σ').2.2 this hxe

/-- A computation reaching `maxReplaySet` is a maximal replay. -/
lemma maxReplaySet_is_maximal_replay {l : Set es.Event} {σ : Computations es.toFamily}
    (h_conf : (Replay.conf es.toFamily σ).1 = maxReplaySet es l)
    (h_compat : σ ⊨ l) :
    Replay.isMaxReplay es.toFamily es.conflict l σ := by
  constructor
  · exact h_compat
  · intro σ' h'_compat
    rw [h_conf]
    intro x hx
    -- hx : x ∈ (Replay.conf es.toFamily σ').1, need to show: x ∈ maxReplaySet es l
    by_cases hconflict : ∃ e', x # e'
    · -- Case 1: x conflicts with something, so by compatibility x ∈ l ⊆ minReplaySet
      obtain ⟨e', hc⟩ := hconflict
      have x_in_l : x ∈ l := h'_compat.2.2 x hx e' hc
      left
      exact minReplaySet_contains_log es x_in_l
    · -- Case 2: x has no conflicts, show it's in the forced set
      right
      intro e₁ e₂ ⟨hmc, hle⟩
      -- e₁ ## e₂ and e₁ ≤ x
      -- Since x ∈ conf(σ') and configurations are downward-closed, e₁ ∈ conf(σ')
      have he₁_in : e₁ ∈ (Replay.conf es.toFamily σ').1 := (Replay.conf es.toFamily σ').2.2 hx hle
      -- From e₁ ## e₂, we have e₁ # e₂ (minimalConflict.1)
      have hconf_e₁_e₂ : e₁ # e₂ := hmc.1
      -- By compatibility of σ': e₁ ∈ conf(σ') and e₁ # e₂ implies e₁ ∈ l
      exact h'_compat.2.2 e₁ he₁_in e₂ hconf_e₁_e₂

/-- The least replay exists when some compatible computation reaches `minReplaySet`. -/
lemma minReplay_exists (l : Set es.Event)
    (hexists : ∃ σ : Computations es.toFamily,
      (Replay.conf es.toFamily σ).1 = minReplaySet es l ∧ σ ⊨ l) :
    ∃ σ : Computations es.toFamily, Replay.isMinReplay es.toFamily es.conflict l σ := by
  obtain ⟨σ, h_conf, h_compat⟩ := hexists
  exact ⟨σ, minReplaySet_is_minimal_replay es h_conf h_compat⟩

/-- A greatest replay exists once some compatible computation reaches
`maxReplaySet`. -/
lemma maxReplay_exists (l : Set es.Event)
    (hexists : ∃ σ : Computations es.toFamily,
      (Replay.conf es.toFamily σ).1 = maxReplaySet es l ∧ σ ⊨ l) :
    ∃ σ : Computations es.toFamily, Replay.isMaxReplay es.toFamily es.conflict l σ := by
  obtain ⟨σ, h_conf, h_compat⟩ := hexists
  exact ⟨σ, maxReplaySet_is_maximal_replay es h_conf h_compat⟩

/-- The downset is a configuration. -/
lemma downset_isConf (e : es.Event) : isConf es (downset es e) :=
  ⟨fun h₁ h₂ hc => es.conflict_irrefl e
     (es.conflict_hereditary (es.conflict_symm.symm _ _ (es.conflict_hereditary hc h₂)) h₁),
   fun hx hle => le_trans hle hx⟩

/-- Inside a configuration, the history of an event is its downset. -/
lemma hist_eq_downset {c : Set es.Event} (hc : isConf es c) {x : es.Event} (hx : x ∈ c) :
    Stable.hist es.toFamily c x = downset es x :=
  Set.Subset.antisymm
    (Stable.hist_least (F := es.toFamily) (downset_isConf es x) (fun _ hy => hc.2 hx hy) le_rfl)
    (fun _ hy => Set.mem_sInter.mpr (fun _ hm => hm.1.2 hm.2.2 hy))

/-- Hence the general least replay set agrees with the prime one. -/
lemma replaySet_eq_minReplaySet {c l : Set es.Event} (hc : isConf es c) (hlc : l ⊆ c) :
    Stable.replaySet es.toFamily c l = minReplaySet es l :=
  Set.iUnion₂_congr (fun _ hy => hist_eq_downset es hc (hlc hy))

end Replay
