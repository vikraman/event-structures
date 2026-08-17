import EventStructures.Prime.Basic
import EventStructures.Prime.Configuration
import EventStructures.LTS.Basic

/-! # The LTSI of a prime event structure -/

variable {L : Type*}

namespace PES

variable (es : PES L)

open Configuration

local infix:50 " ⊢ " => enables es
local infixl:50 " ⋈ " => es.concurrent

/-- The empty configuration. -/
def emptyConfig : Conf es :=
  ⟨∅, fun h _ _ => (Set.notMem_empty _ h).elim,
      fun h _ => (Set.notMem_empty _ h).elim⟩

/-- Forward step: extend by a fresh enabled event. -/
def esStep (c₁ : Conf es) (a : L) (c₂ : Conf es) : Prop :=
  ∃ e, (c₁.1 ⊢ e) ∧ e ∉ c₁.1 ∧ es.label e = a ∧ c₂.1 = c₁.1 ∪ {e}

/-- Coinitial independence: concurrent fresh enabled events. -/
def esIndep (c : Conf es) (a : L) (c₁ : Conf es) (b : L) (c₂ : Conf es) : Prop :=
  ∃ e₁ e₂, (c.1 ⊢ e₁) ∧ (c.1 ⊢ e₂) ∧ e₁ ∉ c.1 ∧ e₂ ∉ c.1 ∧
    es.label e₁ = a ∧ es.label e₂ = b ∧
    c₁.1 = c.1 ∪ {e₁} ∧ c₂.1 = c.1 ∪ {e₂} ∧ e₁ ⋈ e₂

/-- LTSI of an event structure. -/
def toLTSI : LTSI L where
  State := Conf es
  init := emptyConfig es
  step := esStep es
  indep := esIndep es

namespace LPVProof

variable {es}

/-- Concurrent enabled events stay enabled after one fires. -/
lemma enables_after_concurrent {c : Set es.Event} {e₁ e₂ : es.Event}
    (h₁ : c ⊢ e₁) (h₂ : c ⊢ e₂) (hc : e₁ ⋈ e₂) :
    (c ∪ {e₁}) ⊢ e₂ := by
  obtain ⟨_, hCons, hPast⟩ := h₂
  refine ⟨enables_extension (es := es) h₁, ?_, fun x hx => Set.mem_union_left _ (hPast hx)⟩
  rintro e' (he' | he')
  · exact hCons e' he'
  · rw [Set.mem_singleton_iff] at he'; subst he'
    exact fun hConf => hc.1 (es.conflict_symm hConf)

/-- Singleton extensions commute. -/
lemma union_pair_comm (s : Set es.Event) (e₁ e₂ : es.Event) :
    s ∪ {e₁} ∪ {e₂} = s ∪ {e₂} ∪ {e₁} := by
  ext x; simp only [Set.mem_union, Set.mem_singleton_iff]; tauto

end LPVProof

/-- The event-structure LTSI satisfies LPV. -/
theorem toLTSI_LPV : LTSI.LPV (toLTSI es) where
  indep_step_left
    | ⟨e, _, h, _, hfr, _, hlbl, _, htgt, _, _⟩ => ⟨e, h, hfr, hlbl, htgt⟩
  indep_step_right
    | ⟨_, e, _, h, _, hfr, _, hlbl, _, htgt, _⟩ => ⟨e, h, hfr, hlbl, htgt⟩
  indep_irrefl := by
    rintro s a s' ⟨e₁, e₂, _, _, hfr₁, _, _, _, htgt₁, htgt₂, hc⟩
    have hset : s.1 ∪ {e₁} = s.1 ∪ {e₂} := htgt₁.symm.trans htgt₂
    have he : e₁ = e₂ := by
      rcases (hset ▸ Set.mem_union_right s.1 (rfl : e₁ ∈ {e₁})) with h | h
      · exact (hfr₁ h).elim
      · rwa [Set.mem_singleton_iff] at h
    exact es.concurrent_irrefl _ (he ▸ hc)
  indep_symm
    | ⟨e₁, e₂, h₁, h₂, f₁, f₂, l₁, l₂, t₁, t₂, hc⟩ =>
      ⟨e₂, e₁, h₂, h₁, f₂, f₁, l₂, l₁, t₂, t₁, es.concurrent_symm hc⟩
  square := by
    rintro s a s₁ b s₂ ⟨e₁, e₂, h₁, h₂, f₁, f₂, l₁, l₂, t₁, t₂, hc⟩
    have h2' : (s.1 ∪ {e₁}) ⊢ e₂ := LPVProof.enables_after_concurrent h₁ h₂ hc
    have h1' : (s.1 ∪ {e₂}) ⊢ e₁ :=
      LPVProof.enables_after_concurrent h₂ h₁ (es.concurrent_symm hc)
    have hne : e₁ ≠ e₂ := fun h => es.concurrent_irrefl _ (h ▸ hc)
    have fs₁ : e₂ ∉ s₁.1 := by
      rw [t₁]; rintro (h | h)
      · exact f₂ h
      · exact hne.symm (Set.mem_singleton_iff.mp h)
    have fs₂ : e₁ ∉ s₂.1 := by
      rw [t₂]; rintro (h | h)
      · exact f₁ h
      · exact hne (Set.mem_singleton_iff.mp h)
    refine ⟨⟨s.1 ∪ {e₁} ∪ {e₂}, enables_extension (es := es) h2'⟩, ?_, ?_⟩
    · refine ⟨e₂, t₁ ▸ h2', fs₁, l₂, ?_⟩
      change s.1 ∪ {e₁} ∪ {e₂} = s₁.1 ∪ {e₂}; rw [t₁]
    · refine ⟨e₁, t₂ ▸ h1', fs₂, l₁, ?_⟩
      change s.1 ∪ {e₁} ∪ {e₂} = s₂.1 ∪ {e₁}
      rw [t₂]; exact LPVProof.union_pair_comm s.1 e₁ e₂

/-- Reversible step. -/
def esRStep : Conf es → DirLabel L → Conf es → Prop
  | c₁, DirLabel.fwd a, c₂ => esStep es c₁ a c₂
  | c₁, DirLabel.bwd a, c₂ => esStep es c₂ a c₁

/-- Reversible coinitial independence: same direction, concurrent events. -/
def esRIndep : Conf es → DirLabel L → Conf es → DirLabel L → Conf es → Prop
  | c, DirLabel.fwd a, c₁, DirLabel.fwd b, c₂ => esIndep es c a c₁ b c₂
  | _, DirLabel.fwd _, _, DirLabel.bwd _, _ => False
  | _, DirLabel.bwd _, _, DirLabel.fwd _, _ => False
  | c, DirLabel.bwd a, c₁, DirLabel.bwd b, c₂ =>
    ∃ e₁ e₂, (c₁.1 ⊢ e₁) ∧ (c₂.1 ⊢ e₂) ∧ e₁ ∉ c₁.1 ∧ e₂ ∉ c₂.1 ∧
      es.label e₁ = a ∧ es.label e₂ = b ∧
      c.1 = c₁.1 ∪ {e₁} ∧ c.1 = c₂.1 ∪ {e₂} ∧ e₁ ⋈ e₂

/-- Reversible LTSI of an event structure. -/
def toRLTSI : RLTSI L where
  State := Conf es
  init := emptyConfig es
  step := esRStep es
  indep := esRIndep es
  step_rev := Iff.rfl

namespace RLPVProof

variable {es}

/-- Distinct maximal events of a configuration are concurrent. -/
lemma concurrent_of_both_max {c : Conf es} {e₁ e₂ : es.Event}
    (h₁ : e₁ ∈ c.1) (h₂ : e₂ ∈ c.1) (hne : e₁ ≠ e₂)
    (m₁ : ∀ x ∈ c.1, ¬ e₁ < x) (m₂ : ∀ x ∈ c.1, ¬ e₂ < x) : e₁ ⋈ e₂ :=
  ⟨c.2.1 h₁ h₂,
   fun hle => (lt_or_eq_of_le hle).elim (m₁ e₂ h₂) hne,
   fun hle => (lt_or_eq_of_le hle).elim (m₂ e₁ h₁) (fun h => hne h.symm)⟩

/-- The freshly added event is maximal in the extension. -/
lemma evt_max_after_union {c c' : Conf es} {e : es.Event}
    (hfr : e ∉ c'.1) (htgt : c.1 = c'.1 ∪ {e}) :
    ∀ x ∈ c.1, ¬ e < x := by
  intro x hx hlt
  rw [htgt] at hx
  rcases hx with hx | hx
  · exact hfr (c'.2.2 hx hlt.le)
  · rw [Set.mem_singleton_iff] at hx; subst hx; exact lt_irrefl _ hlt

end RLPVProof

/-- The reversible event-structure LTSI satisfies LPV. -/
theorem toRLTSI_LPV : RLTSI.LPV (toRLTSI es) where
  toLPV := by
    refine
      { indep_step_left := ?_, indep_step_right := ?_, indep_irrefl := ?_,
        indep_symm := ?_, square := ?_ }
    · rintro s (a|a) s₁ (b|b) s₂ h <;> try exact h.elim
      all_goals
        obtain ⟨e, _, hen, _, hfr, _, hlbl, _, htgt, _, _⟩ := h
        exact ⟨e, hen, hfr, hlbl, htgt⟩
    · rintro s (a|a) s₁ (b|b) s₂ h <;> try exact h.elim
      all_goals
        obtain ⟨_, e, _, hen, _, hfr, _, hlbl, _, htgt, _⟩ := h
        exact ⟨e, hen, hfr, hlbl, htgt⟩
    · rintro s (a|a) s' h <;>
        obtain ⟨e₁, e₂, _, _, hfr₁, _, _, _, htgt₁, htgt₂, hc⟩ := h
      all_goals
        first
        | (have hset : s.1 ∪ {e₁} = s.1 ∪ {e₂} := htgt₁.symm.trans htgt₂
           have he : e₁ = e₂ := by
             rcases (hset ▸ Set.mem_union_right s.1 (rfl : e₁ ∈ {e₁})) with h | h
             · exact (hfr₁ h).elim
             · rwa [Set.mem_singleton_iff] at h
           exact es.concurrent_irrefl _ (he ▸ hc))
        | (have hset : s'.1 ∪ {e₁} = s'.1 ∪ {e₂} := htgt₁.symm.trans htgt₂
           have he : e₁ = e₂ := by
             rcases (hset ▸ Set.mem_union_right s'.1 (rfl : e₁ ∈ {e₁})) with h | h
             · exact (hfr₁ h).elim
             · rwa [Set.mem_singleton_iff] at h
           exact es.concurrent_irrefl _ (he ▸ hc))
    · rintro s (a|a) s₁ (b|b) s₂ h <;> try exact h.elim
      all_goals
        obtain ⟨e₁, e₂, h₁, h₂, f₁, f₂, l₁, l₂, t₁, t₂, hc⟩ := h
        exact ⟨e₂, e₁, h₂, h₁, f₂, f₁, l₂, l₁, t₂, t₁, es.concurrent_symm hc⟩
    · rintro s (a|a) s₁ (b|b) s₂ h <;> try exact h.elim
      · obtain ⟨e₁, e₂, h₁, h₂, f₁, f₂, l₁, l₂, t₁, t₂, hc⟩ := h
        have h2' : (s.1 ∪ {e₁}) ⊢ e₂ := LPVProof.enables_after_concurrent h₁ h₂ hc
        have h1' : (s.1 ∪ {e₂}) ⊢ e₁ :=
          LPVProof.enables_after_concurrent h₂ h₁ (es.concurrent_symm hc)
        have hne : e₁ ≠ e₂ := fun h => es.concurrent_irrefl _ (h ▸ hc)
        have fs₁ : e₂ ∉ s₁.1 := by
          rw [t₁]; rintro (h | h)
          · exact f₂ h
          · exact hne.symm (Set.mem_singleton_iff.mp h)
        have fs₂ : e₁ ∉ s₂.1 := by
          rw [t₂]; rintro (h | h)
          · exact f₁ h
          · exact hne (Set.mem_singleton_iff.mp h)
        refine ⟨⟨s.1 ∪ {e₁} ∪ {e₂}, enables_extension (es := es) h2'⟩, ?_, ?_⟩
        · refine ⟨e₂, t₁ ▸ h2', fs₁, l₂, ?_⟩
          change s.1 ∪ {e₁} ∪ {e₂} = s₁.1 ∪ {e₂}; rw [t₁]
        · refine ⟨e₁, t₂ ▸ h1', fs₂, l₁, ?_⟩
          change s.1 ∪ {e₁} ∪ {e₂} = s₂.1 ∪ {e₁}
          rw [t₂]; exact LPVProof.union_pair_comm s.1 e₁ e₂
      · -- bwd-bwd SP: closing state is `s \ {e₁, e₂}`.
        obtain ⟨e₁, e₂, h₁, h₂, f₁, f₂, l₁, l₂, t₁, t₂, hc⟩ := h
        have hne : e₁ ≠ e₂ := fun h => es.concurrent_irrefl _ (h ▸ hc)
        have he₁_in_s : e₁ ∈ s.1 := t₁ ▸ Set.mem_union_right _ rfl
        have he₂_in_s : e₂ ∈ s.1 := t₂ ▸ Set.mem_union_right _ rfl
        have hmax₁ : ∀ x ∈ s.1, ¬ e₁ < x :=
          RLPVProof.evt_max_after_union f₁ t₁
        have hmax₂ : ∀ x ∈ s.1, ¬ e₂ < x :=
          RLPVProof.evt_max_after_union f₂ t₂
        -- u = s \ {e₁, e₂}.
        have hu_isConf : isConf es (s.1 \ {e₁, e₂}) := by
          refine ⟨fun hx hy => s.2.1 hx.1 hy.1, ?_⟩
          intro x y hx hy
          refine ⟨s.2.2 hx.1 hy, ?_⟩
          rintro (rfl | rfl)
          · rcases eq_or_lt_of_le hy with rfl | hlt
            · exact hx.2 (Or.inl rfl)
            · exact hmax₁ x hx.1 hlt
          · rcases eq_or_lt_of_le hy with rfl | hlt
            · exact hx.2 (Or.inr rfl)
            · exact hmax₂ x hx.1 hlt
        let u : Conf es := ⟨s.1 \ {e₁, e₂}, hu_isConf⟩
        -- Past of eᵢ lies in u (uses concurrency to exclude the other event).
        have hpast₁ : es.past e₁ ⊆ u.1 := fun x hx => by
          refine ⟨h₁.2.2 hx |> (t₁ ▸ Set.mem_union_left _ ·), ?_⟩
          rintro (rfl | rfl)
          · exact lt_irrefl _ hx
          · exact hc.2.2 hx.le
        have hpast₂ : es.past e₂ ⊆ u.1 := fun x hx => by
          refine ⟨h₂.2.2 hx |> (t₂ ▸ Set.mem_union_left _ ·), ?_⟩
          rintro (rfl | rfl)
          · exact hc.2.1 hx.le
          · exact lt_irrefl _ hx
        have hu_e₁ : u.1 ⊢ e₁ :=
          ⟨hu_isConf, fun x hx hconf => s.2.1 he₁_in_s hx.1 hconf, hpast₁⟩
        have hu_e₂ : u.1 ⊢ e₂ :=
          ⟨hu_isConf, fun x hx hconf => s.2.1 he₂_in_s hx.1 hconf, hpast₂⟩
        have hu_fr₁ : e₁ ∉ u.1 := fun h => h.2 (Or.inl rfl)
        have hu_fr₂ : e₂ ∉ u.1 := fun h => h.2 (Or.inr rfl)
        have he₂_in_s₁ : e₂ ∈ s₁.1 := by
          have hes : e₂ ∈ s.1 := he₂_in_s
          rw [t₁] at hes
          rcases hes with h | h
          · exact h
          · rw [Set.mem_singleton_iff] at h; exact (hne h.symm).elim
        have he₁_in_s₂ : e₁ ∈ s₂.1 := by
          have hes : e₁ ∈ s.1 := he₁_in_s
          rw [t₂] at hes
          rcases hes with h | h
          · exact h
          · rw [Set.mem_singleton_iff] at h; exact (hne h).elim
        -- s₁.1 = u.1 ∪ {e₂}.
        have hs₁_eq : s₁.1 = u.1 ∪ {e₂} := by
          ext x; constructor
          · intro hx
            by_cases hxe₂ : x = e₂
            · exact Or.inr hxe₂
            · have hxs : x ∈ s.1 := t₁ ▸ Set.mem_union_left _ hx
              refine Or.inl ⟨hxs, ?_⟩
              rintro (hxe₁ | hxe₂')
              · exact f₁ (hxe₁ ▸ hx)
              · exact hxe₂ hxe₂'
          · rintro (⟨hxs, hxn⟩ | hxe₂)
            · have hin : x ∈ s₁.1 ∪ {e₁} := t₁ ▸ hxs
              rcases hin with h | h
              · exact h
              · have hxe : x = e₁ := h
                exact absurd (show x ∈ ({e₁, e₂} : Set _) from Or.inl hxe) hxn
            · exact hxe₂ ▸ he₂_in_s₁
        -- s₂.1 = u.1 ∪ {e₁}.
        have hs₂_eq : s₂.1 = u.1 ∪ {e₁} := by
          ext x; constructor
          · intro hx
            by_cases hxe₁ : x = e₁
            · exact Or.inr hxe₁
            · have hxs : x ∈ s.1 := t₂ ▸ Set.mem_union_left _ hx
              refine Or.inl ⟨hxs, ?_⟩
              rintro (hxe₁' | hxe₂)
              · exact hxe₁ hxe₁'
              · exact f₂ (hxe₂ ▸ hx)
          · rintro (⟨hxs, hxn⟩ | hxe₁)
            · have hin : x ∈ s₂.1 ∪ {e₂} := t₂ ▸ hxs
              rcases hin with h | h
              · exact h
              · have hxe : x = e₂ := h
                exact absurd (show x ∈ ({e₁, e₂} : Set _) from Or.inr hxe) hxn
            · exact hxe₁ ▸ he₁_in_s₂
        exact ⟨u, ⟨e₂, hu_e₂, hu_fr₂, l₂, hs₁_eq⟩, ⟨e₁, hu_e₁, hu_fr₁, l₁, hs₂_eq⟩⟩
  BTI := by
    rintro s a s₁ b s₂ ⟨e₁, h₁, f₁, l₁, t₁⟩ ⟨e₂, h₂, f₂, l₂, t₂⟩ hdist
    have hne : e₁ ≠ e₂ := by
      rintro rfl
      apply hdist.elim
      · exact fun hab => hab (l₁.symm.trans l₂)
      · -- s₁ and s₂ both equal s \ {e₁}, so they're equal.
        refine fun hs₁₂ => hs₁₂ (Subtype.ext ?_)
        ext x
        constructor
        · intro hx
          have : x ∈ s.1 := t₁ ▸ Set.mem_union_left _ hx
          rw [t₂] at this
          rcases this with h | h
          · exact h
          · rw [Set.mem_singleton_iff] at h; subst h; exact (f₁ hx).elim
        · intro hx
          have : x ∈ s.1 := t₂ ▸ Set.mem_union_left _ hx
          rw [t₁] at this
          rcases this with h | h
          · exact h
          · rw [Set.mem_singleton_iff] at h; subst h; exact (f₂ hx).elim
    have he₁_in_s : e₁ ∈ s.1 := t₁ ▸ Set.mem_union_right _ rfl
    have he₂_in_s : e₂ ∈ s.1 := t₂ ▸ Set.mem_union_right _ rfl
    have hmax₁ : ∀ x ∈ s.1, ¬ e₁ < x :=
      RLPVProof.evt_max_after_union f₁ t₁
    have hmax₂ : ∀ x ∈ s.1, ¬ e₂ < x :=
      RLPVProof.evt_max_after_union f₂ t₂
    exact ⟨e₁, e₂, h₁, h₂, f₁, f₂, l₁, l₂, t₁, t₂,
           RLPVProof.concurrent_of_both_max he₁_in_s he₂_in_s hne hmax₁ hmax₂⟩

end PES

