import EventStructures.Stable.Basic
import EventStructures.Family.LTSI

/-! # The reversible LTSI of a stable family

Backward steps undo one event. The reverse LPV axioms require stability. -/

open ConfFamily

variable {L : Type*} (F : ConfFamily L)

namespace ConfFamily

/-- Reversible step: forward adds an event, backward removes one. -/
def esRStep : Conf F → DirLabel L → Conf F → Prop
  | c₁, DirLabel.fwd a, c₂ => esStep F c₁ a c₂
  | c₁, DirLabel.bwd a, c₂ => esStep F c₂ a c₁

/-- Reversible coinitial independence: same direction, distinct events. -/
def esRIndep : Conf F → DirLabel L → Conf F → DirLabel L → Conf F → Prop
  | c, DirLabel.fwd a, c₁, DirLabel.fwd b, c₂ => esIndep F c a c₁ b c₂
  | _, DirLabel.fwd _, _, DirLabel.bwd _, _ => False
  | _, DirLabel.bwd _, _, DirLabel.fwd _, _ => False
  | c, DirLabel.bwd a, c₁, DirLabel.bwd b, c₂ =>
      ∃ e₁ e₂, e₁ ≠ e₂ ∧ e₁ ∈ c.val ∧ e₂ ∈ c.val ∧
        F.label e₁ = a ∧ F.label e₂ = b ∧
        F.Config (c.val \ {e₁}) ∧ F.Config (c.val \ {e₂}) ∧
        c₁.val = c.val \ {e₁} ∧ c₂.val = c.val \ {e₂}

/-- The reversible LTSI of a configuration family. -/
def toRLTSI : RLTSI L where
  State := Conf F
  init := ConfFamily.empty F
  step := esRStep F
  indep := esRIndep F
  step_rev := Iff.rfl

variable {F}

/-- Removing and re-adding a present event leaves a configuration unchanged. -/
lemma union_diff_singleton {c : Set F.Event} {e : F.Event} (he : e ∈ c) :
    (c \ {e}) ∪ {e} = c := by
  ext x
  constructor
  · rintro (⟨hx, -⟩ | hx)
    · exact hx
    · exact (Set.mem_singleton_iff.mp hx) ▸ he
  · intro hx
    by_cases hxe : x = e
    · exact Or.inr (Set.mem_singleton_iff.mpr hxe)
    · exact Or.inl ⟨hx, fun h => hxe (Set.mem_singleton_iff.mp h)⟩

/-- A backward step is a forward step read the other way. -/
lemma esRStep_bwd {c c' : Conf F} {a : L} {e : F.Event}
    (hc : F.Config c'.val) (he : e ∈ c.val) (hlbl : F.label e = a)
    (htgt : c'.val = c.val \ {e}) : esRStep F c (DirLabel.bwd a) c' :=
  ⟨e, ⟨hc, by rw [htgt, union_diff_singleton he]; exact c.2⟩,
   by rw [htgt]; exact fun h => h.2 rfl, hlbl,
   by rw [htgt, union_diff_singleton he]⟩

/-- The closing state of two backward steps. -/
lemma config_diff_pair (hF : Stable F) {c : Set F.Event} {e₁ e₂ : F.Event}
    (h₁ : F.Config (c \ {e₁})) (h₂ : F.Config (c \ {e₂})) (hc : F.Config c) :
    F.Config ((c \ {e₁}) ∩ (c \ {e₂})) := by
  have hpair : ((c \ {e₁}) ∩ (c \ {e₂})) = ⋂₀ {c \ {e₁}, c \ {e₂}} := by
    rw [Set.sInter_pair]
  rw [hpair]
  refine hF ⟨c \ {e₁}, Or.inl rfl⟩ ?_ hc ?_
  · rintro x (rfl | rfl)
    · exact h₁
    · exact h₂
  · rintro x (rfl | rfl) <;> exact fun _ hy => hy.1

/-- Re-adding one of the two removed events. -/
lemma inter_diff_union {c : Set F.Event} {e₁ e₂ : F.Event}
    (he₂ : e₂ ∈ c) (hne : e₁ ≠ e₂) :
    ((c \ {e₁}) ∩ (c \ {e₂})) ∪ {e₂} = c \ {e₁} := by
  ext x
  constructor
  · rintro (⟨hx, -⟩ | hx)
    · exact hx
    · exact (Set.mem_singleton_iff.mp hx) ▸ ⟨he₂, fun h => hne (Set.mem_singleton_iff.mp h).symm⟩
  · rintro ⟨hx, hx₁⟩
    by_cases hxe : x = e₂
    · exact Or.inr (Set.mem_singleton_iff.mpr hxe)
    · exact Or.inl ⟨⟨hx, hx₁⟩, ⟨hx, fun h => hxe (Set.mem_singleton_iff.mp h)⟩⟩

/-- Re-adding the other one. -/
lemma inter_diff_union' {c : Set F.Event} {e₁ e₂ : F.Event}
    (he₁ : e₁ ∈ c) (hne : e₁ ≠ e₂) :
    ((c \ {e₁}) ∩ (c \ {e₂})) ∪ {e₁} = c \ {e₂} := by
  rw [Set.inter_comm]; exact inter_diff_union he₁ hne.symm

/-- The reversible LTSI of a stable family satisfies the reverse LPV axioms. -/
theorem toRLTSI_LPV (hF : Stable F) : RLTSI.LPV (toRLTSI F) where
  toLPV := by
    refine { indep_step_left := ?_, indep_step_right := ?_, indep_irrefl := ?_,
             indep_symm := ?_, square := ?_ }
    · rintro s (a | a) s₁ (b | b) s₂ h <;> try exact h.elim
      · exact (toLTSI_LPV F).indep_step_left h
      · obtain ⟨e₁, -, -, hin₁, -, hl₁, -, hc₁, -, ht₁, -⟩ := h
        exact esRStep_bwd (by rw [ht₁]; exact hc₁) hin₁ hl₁ ht₁
    · rintro s (a | a) s₁ (b | b) s₂ h <;> try exact h.elim
      · exact (toLTSI_LPV F).indep_step_right h
      · obtain ⟨-, e₂, -, -, hin₂, -, hl₂, -, hc₂, -, ht₂⟩ := h
        exact esRStep_bwd (by rw [ht₂]; exact hc₂) hin₂ hl₂ ht₂
    · rintro s (a | a) s' h
      · exact (toLTSI_LPV F).indep_irrefl h
      · obtain ⟨e₁, e₂, hne, hin₁, -, -, -, -, -, ht₁, ht₂⟩ := h
        refine hne ?_
        have : e₁ ∉ s'.val := by rw [ht₁]; exact fun hx => hx.2 rfl
        rw [ht₂] at this
        by_contra hne'
        exact this ⟨hin₁, fun h => hne' (Set.mem_singleton_iff.mp h)⟩
    · rintro s (a | a) s₁ (b | b) s₂ h <;> try exact h.elim
      · exact (toLTSI_LPV F).indep_symm h
      · obtain ⟨e₁, e₂, hne, hin₁, hin₂, hl₁, hl₂, hc₁, hc₂, ht₁, ht₂⟩ := h
        exact ⟨e₂, e₁, hne.symm, hin₂, hin₁, hl₂, hl₁, hc₂, hc₁, ht₂, ht₁⟩
    · rintro s (a | a) s₁ (b | b) s₂ h <;> try exact h.elim
      · exact (toLTSI_LPV F).square h
      · obtain ⟨e₁, e₂, hne, hin₁, hin₂, hl₁, hl₂, hc₁, hc₂, ht₁, ht₂⟩ := h
        refine ⟨⟨(s.val \ {e₁}) ∩ (s.val \ {e₂}), config_diff_pair hF hc₁ hc₂ s.2⟩, ?_, ?_⟩
        · refine ⟨e₂, ⟨config_diff_pair hF hc₁ hc₂ s.2, ?_⟩, ?_, hl₂, ?_⟩
          · rw [inter_diff_union hin₂ hne]; exact hc₁
          · exact fun hx => hx.2.2 rfl
          · rw [ht₁, inter_diff_union hin₂ hne]
        · refine ⟨e₁, ⟨config_diff_pair hF hc₁ hc₂ s.2, ?_⟩, ?_, hl₁, ?_⟩
          · rw [inter_diff_union' hin₁ hne]; exact hc₂
          · exact fun hx => hx.1.2 rfl
          · rw [ht₂, inter_diff_union' hin₁ hne]
  BTI := by
    intro s a s₁ b s₂ h₁ h₂ hdist
    obtain ⟨e₁, hen₁, hfr₁, hl₁, ht₁⟩ := h₁
    obtain ⟨e₂, hen₂, hfr₂, hl₂, ht₂⟩ := h₂
    have hin₁ : e₁ ∈ s.val := ht₁ ▸ Set.mem_union_right _ rfl
    have hin₂ : e₂ ∈ s.val := ht₂ ▸ Set.mem_union_right _ rfl
    have hd₁ : s₁.val = s.val \ {e₁} := by
      rw [ht₁]; ext x
      constructor
      · exact fun hx => ⟨Or.inl hx, fun h => hfr₁ ((Set.mem_singleton_iff.mp h) ▸ hx)⟩
      · rintro ⟨hx | hx, hne⟩
        · exact hx
        · exact absurd (Set.mem_singleton_iff.mp hx) (fun h => hne (h ▸ rfl))
    have hd₂ : s₂.val = s.val \ {e₂} := by
      rw [ht₂]; ext x
      constructor
      · exact fun hx => ⟨Or.inl hx, fun h => hfr₂ ((Set.mem_singleton_iff.mp h) ▸ hx)⟩
      · rintro ⟨hx | hx, hne⟩
        · exact hx
        · exact absurd (Set.mem_singleton_iff.mp hx) (fun h => hne (h ▸ rfl))
    have hne : e₁ ≠ e₂ := by
      rintro rfl
      exact hdist.elim (fun hab => hab (hl₁.symm.trans hl₂))
        (fun hs => hs (Subtype.ext (hd₁.trans hd₂.symm)))
    exact ⟨e₁, e₂, hne, hin₁, hin₂, hl₁, hl₂, hd₁ ▸ s₁.2, hd₂ ▸ s₂.2, hd₁, hd₂⟩

end ConfFamily
