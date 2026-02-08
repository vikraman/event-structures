import EventStructures.Configuration
import EventStructures.Path
import EventStructures.FinitePoset
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite.Basic

variable (es : EventStructure)

namespace Rollback

open Configuration
local infix:50 " ⊢ " => enables es

/-- A rollback of event `e` on configuration `c` is a maximal configuration `m`
    with `m ⊆ c` and `e ∉ m`. -/
def isRollback (c : Conf es) (e : es.Event) (m : Conf es) : Prop :=
  m.1 ⊆ c.1 ∧ e ∉ m.1 ∧
  ∀ m' : Conf es, m'.1 ⊆ c.1 → e ∉ m'.1 → m.1 ⊆ m'.1 → m'.1 ⊆ m.1

/-- The set of all rollbacks of event `e` on configuration `c`. -/
def Rollbacks (c : Conf es) (e : es.Event) : Set (Conf es) :=
  {m | isRollback es c e m}

/-- Candidate configurations for rollback. -/
def RollbackCandidates (c : Conf es) (e : es.Event) : Set (Conf es) :=
  {m | m.1 ⊆ c.1 ∧ e ∉ m.1}

@[simp] lemma rollback_subset {c : Conf es} {e : es.Event} {m : Conf es}
    (h : isRollback es c e m) : m.1 ⊆ c.1 :=
  h.1

@[simp] lemma rollback_not_mem {c : Conf es} {e : es.Event} {m : Conf es}
    (h : isRollback es c e m) : e ∉ m.1 :=
  h.2.1

lemma rollback_maximal {c : Conf es} {e : es.Event} {m : Conf es}
    (h : isRollback es c e m) :
    ∀ m' : Conf es, m'.1 ⊆ c.1 → e ∉ m'.1 → m.1 ⊆ m'.1 → m'.1 ⊆ m.1 :=
  h.2.2

lemma isRollback_iff_maximal {c : Conf es} {e : es.Event} {m : Conf es} :
    isRollback es c e m ↔ m ∈ RollbackCandidates es c e ∧
      ∀ m' : Conf es, m' ∈ RollbackCandidates es c e → m.1 ⊆ m'.1 → m'.1 ⊆ m.1 := by
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

lemma rollback_subset_future {c : Conf es} {e : es.Event} {m : Conf es}
    (h : isRollback es c e m) : m.1 ⊆ c.1 \ es.future e := by
  intro x hx
  refine ⟨h.1 hx, ?_⟩
  intro hxFuture
  have hle : e ≤ x := hxFuture
  have hemem : e ∈ m.1 := (m.2).2 hx hle
  exact h.2.1 hemem

/-- Removing the future of `e` from a configuration keeps it a configuration. -/
lemma rollback_future_isConf {c : Conf es} {e : es.Event} :
    isConf es (c.1 \ es.future e) := by
  constructor
  · intro e₁ e₂ h₁ h₂
    rcases h₁ with ⟨h₁c, _⟩
    rcases h₂ with ⟨h₂c, _⟩
    exact c.2.1 h₁c h₂c
  · intro x y hx hy
    rcases hx with ⟨hxc, hxf⟩
    refine ⟨c.2.2 hxc hy, ?_⟩
    intro hyf
    have hle : e ≤ x := le_trans hyf hy
    exact hxf hle

/-- The canonical rollback configuration: remove all events causally after `e`. -/
def rollbackFuture (c : Conf es) (e : es.Event) : Conf es :=
  ⟨c.1 \ es.future e, rollback_future_isConf (es := es) (c := c)⟩

@[simp] lemma rollbackFuture_val (c : Conf es) (e : es.Event) :
    (@rollbackFuture es c e).1 = c.1 \ es.future e :=
  rfl

@[simp] lemma rollbackFuture_mem {c : Conf es} {e : es.Event} {x : es.Event} :
    x ∈ (@rollbackFuture es c e).1 ↔ x ∈ c.1 ∧ x ∉ es.future e :=
  Iff.rfl

/-- Redoability: `e` is enabled in `rollback(c,e)` when `e ∈ c`. -/
lemma rollback_redoable {c : Conf es} {e : es.Event} (he : e ∈ c.1) :
    (@rollbackFuture es c e).1 ⊢ e := by
  constructor
  · exact rollback_future_isConf (es := es) (c := c)
  constructor
  · -- All events in rollback are consistent with e
    intro e' he'
    exact c.2.1 he he'.1
  · -- The strict past of e is contained in rollback
    intro x hx
    have hxc : x ∈ c.1 := c.2.2 he (le_of_lt hx)
    have hxnot : x ∉ es.future e := fun h => not_le_of_gt hx h
    exact ⟨hxc, hxnot⟩

/-- Causal safety: Rollback removes exactly the causal consequences of `e`. -/
lemma rollback_causal_safety {c : Conf es} {e : es.Event} {x : es.Event} :
    x ∈ (@rollbackFuture es c e).1 → x ∉ es.future e :=
  fun hx => hx.2

/-- The canonical rollback is a rollback for `c` and `e`. -/
lemma rollback_future {c : Conf es} {e : es.Event} :
    isRollback es c e (@rollbackFuture es c e) := by
  constructor
  · exact fun _ hx => hx.1  -- Subset of c
  constructor
  · exact fun he => he.2 le_rfl  -- e not in rollback
  · -- Maximality
    intro m' hm'sub hm'not _ _ hx
    have hxc : _ ∈ c.1 := hm'sub hx
    have hxnot : _ ∉ es.future e := fun h => hm'not (m'.2.2 hx h)
    exact ⟨hxc, hxnot⟩

/-- Any rollback coincides with the canonical rollback. -/
@[simp] lemma rollback_eq_future {c : Conf es} {e : es.Event} {m : Conf es}
    (h : isRollback es c e m) : m.1 = c.1 \ es.future e := by
  apply Set.Subset.antisymm
  · exact rollback_subset_future (es := es) h
  · -- The canonical rollback is also a candidate, so m must contain it by maximality
    have hsub : c.1 \ es.future e ⊆ c.1 := fun x hx => hx.1
    have hnot : e ∉ c.1 \ es.future e := fun he => he.2 le_rfl
    exact h.2.2 (@rollbackFuture es c e) hsub hnot (rollback_subset_future (es := es) h)

/-- Rollbacks are unique when they exist. -/
lemma rollback_unique {c : Conf es} {e : es.Event}
    {m₁ m₂ : Conf es} (h₁ : isRollback es c e m₁) (h₂ : isRollback es c e m₂) :
    m₁ = m₂ := by
  apply Subtype.ext
  rw [rollback_eq_future (es := es) h₁, rollback_eq_future (es := es) h₂]

/-- The rollback is the maximum element among rollback candidates. -/
lemma rollback_maximum {c : Conf es} {e : es.Event} {m : Conf es}
    (h : isRollback es c e m) :
    ∀ m' : Conf es, m' ∈ RollbackCandidates es c e → m'.1 ⊆ m.1 := by
  -- By uniqueness, m equals the canonical rollback
  have : m = @rollbackFuture es c e := rollback_unique (es := es) h (rollback_future (es := es))
  cases this
  -- Now show any candidate is a subset of the canonical rollback
  intro m' ⟨hm'sub, hm'not⟩ x hx
  exact ⟨hm'sub hx, fun hxFuture => hm'not (m'.2.2 hx hxFuture)⟩

/-- Helper: An event in the future is enabled in a partial configuration that
    contains its strict past and is consistent. -/
lemma event_enabled_when_past_present {c : Conf es} {e x : es.Event}
    (hx : x ∈ c.1 ∩ es.future e) (c' : Conf es)
    (hpast : ∀ y, y < x → y ∈ c.1 ∩ es.future e → y ∈ c'.1)
    (hbase : (@rollbackFuture es c e).1 ⊆ c'.1)
    (hconf : c'.1 ⊆ c.1) :
    c'.1 ⊢ x := by
  constructor
  · exact c'.2
  constructor
  · -- Consistency: x is consistent with all events in c'
    intro y hy
    have hyc : y ∈ c.1 := hconf hy
    exact c.2.1 hx.1 hyc
  · -- Past: the strict past of x is in c'
    intro y hy
    by_cases hyf : y ∈ es.future e
    · -- y is in the future of e, so it was added before x
      have hyc : y ∈ c.1 := c.2.2 hx.1 (le_of_lt hy)
      exact hpast y hy ⟨hyc, hyf⟩
    · -- y is not in the future of e, so it's in the rollback
      have hyc : y ∈ c.1 := c.2.2 hx.1 (le_of_lt hy)
      exact hbase ⟨hyc, hyf⟩

/-- CONJECTURE: For finite configurations, an executable list from rollback to the original
    configuration exists. -/
theorem execList_exists_finite [WellFoundedLT es.Event] {c : Conf es} {e : es.Event}
    (hfin : (c.1 ∩ es.future e).Finite) :
    Nonempty (Σ t : List es.Event, Path.ExecList es (@rollbackFuture es c e) t c) := by
  sorry

/-- Correctness: The original configuration `c` is reachable from `rollback(c,e)`
    when the future is finite and < is well-founded. -/
lemma rollback_correctness_finite [WellFoundedLT es.Event] {c : Conf es} {e : es.Event}
    (hfin : (c.1 ∩ es.future e).Finite) :
    Nonempty (Path es (@rollbackFuture es c e) c) := by
  obtain ⟨⟨t, hExec⟩⟩ := execList_exists_finite (es := es) hfin
  exact ⟨Path.execList_to_path (es := es) hExec⟩

/-- CONJECTURE: Minimality of Rollback - Any path from a candidate configuration to `c` is at
    least as long as the path from `rollback(c,e)` to `c`. -/
lemma rollback_minimality {c : Conf es} {e : es.Event}
    (p : Path es (@rollbackFuture es c e) c)
    (c' : Conf es) (hredo : c'.1 ⊢ e) (hsafe : ∀ x ∈ c'.1, x ∉ es.future e)
    (p' : Path es c' c) :
    Path.length es p ≤ Path.length es p' := by
  sorry

end Rollback
