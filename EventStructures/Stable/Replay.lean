import EventStructures.Stable.Basic
import EventStructures.Family.Replay

/-! # Least replay sets

Relative to a bounding configuration `c`, the least subconfiguration of `c`
containing a log `l` is the union of the histories of the events of `l`. -/

open ConfFamily

variable {L : Type*} {F : ConfFamily L}

namespace Stable

/-- The least subconfiguration of `c` containing `l`. -/
def replaySet (F : ConfFamily L) (c l : Set F.Event) : Set F.Event :=
  ⋃ x ∈ l, hist F c x

variable {c l : Set F.Event} (hc : F.Config c) (hlc : l ⊆ c)

omit hc hlc in
lemma subset_replaySet : l ⊆ replaySet F c l :=
  fun _ hx => Set.mem_biUnion hx hist_mem

include hc hlc in
lemma replaySet_subset : replaySet F c l ⊆ c := by
  rintro x hx
  obtain ⟨-, ⟨y, rfl⟩, -, ⟨hy, rfl⟩, hxy⟩ := hx
  exact hist_subset hc (hlc hy) hxy

include hc hlc in
/-- It is a configuration: each history is one by stability, their union by coherence. -/
lemma replaySet_config (hS : Stable F) (hC : Coherent F) : F.Config (replaySet F c l) := by
  have himg : replaySet F c l = ⋃₀ (hist F c '' l) := by
    rw [Set.sUnion_image]; rfl
  rw [himg]
  exact hC (z := c) (by rintro - ⟨y, hy, rfl⟩; exact hist_config hS hc (hlc hy))
    hc (by rintro - ⟨y, hy, rfl⟩; exact hist_subset hc (hlc hy))

omit hc hlc in
/-- It is least among subconfigurations of `c` containing `l`. -/
lemma replaySet_least {m : Set F.Event} (hm : F.Config m) (hmc : m ⊆ c) (hlm : l ⊆ m) :
    replaySet F c l ⊆ m := by
  rintro x hx
  obtain ⟨-, ⟨y, rfl⟩, -, ⟨hy, rfl⟩, hxy⟩ := hx
  exact hist_least hm hmc (hlm hy) hxy

end Stable
