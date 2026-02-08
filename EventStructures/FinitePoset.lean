import Mathlib.Data.Finset.Basic
import Mathlib.Order.WellFounded

/-- A non-empty finite subset of a well-founded partial order has a minimal element. -/
lemma Finset.exists_minimal_of_nonempty {α : Type*} [PartialOrder α] [WellFoundedLT α]
    (T : Finset α) (hne : T.Nonempty) :
    ∃ x ∈ T, ∀ y ∈ T, y < x → False := by
  classical
  obtain ⟨x₀, hx₀⟩ := hne
  -- For any element in T, find minimal below it
  suffices ∀ x, x ∈ T → ∃ m ∈ T, (∀ y ∈ T, y < m → False) ∧ m ≤ x by
    obtain ⟨m, hmT, hmmin, _⟩ := this x₀ hx₀
    exact ⟨m, hmT, hmmin⟩
  intro x
  apply (IsWellFounded.wf (r := (· < ·))).induction x
  intro z ih hz
  by_cases hmin : ∀ y ∈ T, y < z → False
  · exact ⟨z, hz, hmin, le_rfl⟩
  · push_neg at hmin
    obtain ⟨y, hyT, hy_lt, _⟩ := hmin
    obtain ⟨m, hmT, hmmin, hm_le⟩ := ih y hy_lt hyT
    exact ⟨m, hmT, hmmin, le_trans hm_le (le_of_lt hy_lt)⟩
