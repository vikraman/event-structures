import EventStructures.General.Stable
import EventStructures.Stable.Basic
import EventStructures.CCS.Syntax

/-! # Parallel composition

Events are *tags*: an event of the left component, one of the right, or a
label-matched synchronisation. A set of tags is consistent when each component
event is consumed once and each projection is consistent in its component, and
it enables a tag when each event the tag consumes is enabled in its component. -/

open GES

namespace CCS

variable {Name : Type*}

/-- A product event: an `E`-event, an `F`-event, or a label-matched synchronisation. -/
inductive Tag (E F : SES (Action Name)) where
  | left : E.Event → Tag E F
  | right : F.Event → Tag E F
  | sync (e : E.Event) (f : F.Event)
      (h : ∃ a, E.label e = .vis a ∧ F.label f = .vis a.co) : Tag E F

namespace Tag

variable {E F : SES (Action Name)}

/-- The `E`-event a tag consumes. -/
def evL : Tag E F → Option E.Event
  | left e => some e
  | right _ => none
  | sync e _ _ => some e

/-- The `F`-event a tag consumes. -/
def evR : Tag E F → Option F.Event
  | left _ => none
  | right f => some f
  | sync _ f _ => some f

/-- Synchronisations are silent. -/
def label : Tag E F → Action Name
  | left e => E.label e
  | right f => F.label f
  | sync .. => .tau

end Tag

variable {E F : SES (Action Name)}

/-- `E`-events consumed by a set of tags. -/
def projL (C : Set (Tag E F)) : Set E.Event := {e | ∃ t ∈ C, t.evL = some e}

/-- `F`-events consumed by a set of tags. -/
def projR (C : Set (Tag E F)) : Set F.Event := {f | ∃ t ∈ C, t.evR = some f}

lemma projL_mono {C D : Set (Tag E F)} (h : C ⊆ D) : projL C ⊆ projL D :=
  fun _ ⟨t, ht, he⟩ => ⟨t, h ht, he⟩

lemma projR_mono {C D : Set (Tag E F)} (h : C ⊆ D) : projR C ⊆ projR D :=
  fun _ ⟨t, ht, he⟩ => ⟨t, h ht, he⟩

lemma projL_union (C D : Set (Tag E F)) : projL (C ∪ D) = projL C ∪ projL D := by
  ext e
  constructor
  · rintro ⟨t, ht | ht, he⟩
    · exact Or.inl ⟨t, ht, he⟩
    · exact Or.inr ⟨t, ht, he⟩
  · rintro (⟨t, ht, he⟩ | ⟨t, ht, he⟩)
    · exact ⟨t, Or.inl ht, he⟩
    · exact ⟨t, Or.inr ht, he⟩

lemma projR_union (C D : Set (Tag E F)) : projR (C ∪ D) = projR C ∪ projR D := by
  ext f
  constructor
  · rintro ⟨t, ht | ht, he⟩
    · exact Or.inl ⟨t, ht, he⟩
    · exact Or.inr ⟨t, ht, he⟩
  · rintro (⟨t, ht, he⟩ | ⟨t, ht, he⟩)
    · exact ⟨t, Or.inl ht, he⟩
    · exact ⟨t, Or.inr ht, he⟩

lemma projL_empty : projL (∅ : Set (Tag E F)) = ∅ := by ext e; simp [projL]

lemma projR_empty : projR (∅ : Set (Tag E F)) = ∅ := by ext f; simp [projR]

lemma projL_singleton (t : Tag E F) : projL {t} = {e | t.evL = some e} := by
  ext e
  constructor
  · rintro ⟨t', ht', he⟩; rw [Set.mem_singleton_iff] at ht'; exact ht' ▸ he
  · intro he; exact ⟨t, rfl, he⟩

lemma projR_singleton (t : Tag E F) : projR {t} = {f | t.evR = some f} := by
  ext f
  constructor
  · rintro ⟨t', ht', he⟩; rw [Set.mem_singleton_iff] at ht'; exact ht' ▸ he
  · intro he; exact ⟨t, rfl, he⟩

lemma projL_finite {C : Set (Tag E F)} (h : C.Finite) : (projL C).Finite := by
  have : projL C = ⋃ t ∈ C, {e | t.evL = some e} := by ext e; simp [projL]
  rw [this]
  refine h.biUnion (fun t _ => ?_)
  cases ht : t.evL with
  | none => simp
  | some x =>
    refine (Set.finite_singleton x).subset (fun e he => ?_)
    simp only [Set.mem_ofPred_eq, Option.some.injEq] at he
    simp [he]

lemma projR_finite {C : Set (Tag E F)} (h : C.Finite) : (projR C).Finite := by
  have : projR C = ⋃ t ∈ C, {f | t.evR = some f} := by ext f; simp [projR]
  rw [this]
  refine h.biUnion (fun t _ => ?_)
  cases ht : t.evR with
  | none => simp
  | some y =>
    refine (Set.finite_singleton y).subset (fun f hf => ?_)
    simp only [Set.mem_ofPred_eq, Option.some.injEq] at hf
    simp [hf]

/-- Consistency of a pair of tags: no component event consumed twice. -/
def ParCon₂ (t₁ t₂ : Tag E F) : Prop :=
  (∀ e, t₁.evL = some e → t₂.evL = some e → t₁ = t₂) ∧
  (∀ f, t₁.evR = some f → t₂.evR = some f → t₁ = t₂)

/-- Each component event consumed once, and consistent projections. -/
def ParCon (X : Finset (Tag E F)) : Prop :=
  (∀ t₁ ∈ X, ∀ t₂ ∈ X, ParCon₂ t₁ t₂) ∧
  E.toGES.Consistent (projL (X : Set (Tag E F))) ∧
  F.toGES.Consistent (projR (X : Set (Tag E F)))

/-- Enabling: each consumed event is enabled in its component. -/
def ParEnable (X : Finset (Tag E F)) (t : Tag E F) : Prop :=
  (∀ e, t.evL = some e →
    ∃ Y : Finset E.Event, (∀ e' ∈ Y, e' ∈ projL (X : Set (Tag E F))) ∧ E.enable Y e) ∧
  (∀ f, t.evR = some f →
    ∃ Y : Finset F.Event, (∀ f' ∈ Y, f' ∈ projR (X : Set (Tag E F))) ∧ F.enable Y f)

/-- A finite set of events covered by a set of tags is covered by finitely many. -/
lemma exists_cover_L {s : Set (Tag E F)} (V : Finset E.Event) (hV : ↑V ⊆ projL s) :
    ∃ W : Finset (Tag E F), ↑W ⊆ s ∧ ↑V ⊆ projL (W : Set (Tag E F)) := by
  classical
  have hpick : ∀ v ∈ V, ∃ u, u ∈ s ∧ u.evL = some v := fun v hv => hV (by exact_mod_cast hv)
  refine ⟨V.attach.image fun v => (hpick v.1 v.2).choose, ?_, ?_⟩
  · intro u hu
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp (by exact_mod_cast hu)
    exact (hpick v.1 v.2).choose_spec.1
  · intro v hv
    have hv' : v ∈ V := by exact_mod_cast hv
    refine ⟨(hpick v hv').choose, ?_, (hpick v hv').choose_spec.2⟩
    have : (hpick v hv').choose ∈ V.attach.image fun z => (hpick z.1 z.2).choose :=
      Finset.mem_image.mpr ⟨⟨v, hv'⟩, Finset.mem_attach _ _, rfl⟩
    exact_mod_cast this

lemma exists_cover_R {s : Set (Tag E F)} (V : Finset F.Event) (hV : ↑V ⊆ projR s) :
    ∃ W : Finset (Tag E F), ↑W ⊆ s ∧ ↑V ⊆ projR (W : Set (Tag E F)) := by
  classical
  have hpick : ∀ v ∈ V, ∃ u, u ∈ s ∧ u.evR = some v := fun v hv => hV (by exact_mod_cast hv)
  refine ⟨V.attach.image fun v => (hpick v.1 v.2).choose, ?_, ?_⟩
  · intro u hu
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp (by exact_mod_cast hu)
    exact (hpick v.1 v.2).choose_spec.1
  · intro v hv
    have hv' : v ∈ V := by exact_mod_cast hv
    refine ⟨(hpick v hv').choose, ?_, (hpick v hv').choose_spec.2⟩
    have : (hpick v hv').choose ∈ V.attach.image fun z => (hpick z.1 z.2).choose :=
      Finset.mem_image.mpr ⟨⟨v, hv'⟩, Finset.mem_attach _ _, rfl⟩
    exact_mod_cast this

/-- Consistency of a set of tags gives consistency of its left projection. -/
lemma con_projL {s : Set (Tag E F)} (h : ∀ W : Finset (Tag E F), ↑W ⊆ s → ParCon W) :
    E.toGES.Consistent (projL s) := by
  intro V hV
  obtain ⟨W, hWs, hVW⟩ := exists_cover_L V hV
  exact (h W hWs).2.1 V hVW

lemma con_projR {s : Set (Tag E F)} (h : ∀ W : Finset (Tag E F), ↑W ⊆ s → ParCon W) :
    F.toGES.Consistent (projR s) := by
  intro V hV
  obtain ⟨W, hWs, hVW⟩ := exists_cover_R V hV
  exact (h W hWs).2.2 V hVW

lemma parCon_subset {X Y : Finset (Tag E F)} (h : ParCon Y) (hsub : X ⊆ Y) : ParCon X := by
  have hL : projL (X : Set (Tag E F)) ⊆ projL (Y : Set (Tag E F)) :=
    projL_mono (by exact_mod_cast hsub)
  have hR : projR (X : Set (Tag E F)) ⊆ projR (Y : Set (Tag E F)) :=
    projR_mono (by exact_mod_cast hsub)
  exact ⟨fun t₁ h₁ t₂ h₂ => h.1 t₁ (hsub h₁) t₂ (hsub h₂),
         fun W hW => h.2.1 W (hW.trans hL),
         fun W hW => h.2.2 W (hW.trans hR)⟩

/-- Parallel composition, as a stable event structure. -/
@[reducible] def parSES (E F : SES (Action Name)) : SES (Action Name) where
  Event := Tag E F
  Con := ParCon
  enable := ParEnable
  label := Tag.label
  con_empty := by
    refine ⟨fun t ht => absurd ht (Finset.notMem_empty t), ?_, ?_⟩ <;>
      · intro W hW
        have hE : W = ∅ := by
          refine Finset.eq_empty_of_forall_notMem fun z hz => ?_
          obtain ⟨u, hu, -⟩ := hW (by exact_mod_cast hz)
          simp at hu
        first
          | exact hE ▸ E.con_empty
          | exact hE ▸ F.con_empty
  con_subset := parCon_subset
  enable_mono h hsub _ :=
    ⟨fun e he => (h.1 e he).imp fun _ hY =>
       ⟨fun e' he' => projL_mono (by exact_mod_cast hsub) (hY.1 e' he'), hY.2⟩,
     fun f hf => (h.2 f hf).imp fun _ hY =>
       ⟨fun f' hf' => projR_mono (by exact_mod_cast hsub) (hY.1 f' hf'), hY.2⟩⟩
  enable_inter := by
    classical
    rintro X Y Z t hX hY hcons hZ
    have hmemZ : ∀ {u : Tag E F}, u ∈ X → u ∈ Y → u ∈ (Z : Set (Tag E F)) :=
      fun h₁ h₂ => hZ ▸ ⟨by exact_mod_cast h₁, by exact_mod_cast h₂⟩
    have hpair : ∀ {t₁ t₂ : Tag E F}, t₁ ∈ X → t₂ ∈ Y → ParCon₂ t₁ t₂ := by
      intro t₁ t₂ h₁ h₂
      refine (hcons {t₁, t₂} fun u hu => ?_).1 t₁ (Finset.mem_insert_self _ _) t₂
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      rcases Finset.mem_insert.mp (by exact_mod_cast hu) with rfl | hu'
      · exact Or.inl (Or.inl (by exact_mod_cast h₁))
      · exact Or.inl (Or.inr (by rw [Finset.mem_singleton.mp hu']; exact_mod_cast h₂))
    have hsubL : ∀ {V : Finset E.Event} {W : Finset (Tag E F)},
        (∀ e' ∈ V, e' ∈ projL (W : Set (Tag E F))) → ↑W ⊆ (X : Set (Tag E F)) →
        ↑V ⊆ projL ((X : Set (Tag E F)) ∪ ↑Y ∪ {t}) := by
      intro V W hVW hWX v hv
      obtain ⟨u, hu, hev⟩ := hVW v (by exact_mod_cast hv)
      exact ⟨u, Or.inl (Or.inl (hWX hu)), hev⟩
    constructor
    · rintro e he
      obtain ⟨YX, hYX, henX⟩ := hX.1 e he
      obtain ⟨YY, hYY, henY⟩ := hY.1 e he
      refine ⟨YX ∩ YY, fun e' he' => ?_,
        E.enable_inter henX henY (fun V hV => con_projL hcons V (hV.trans ?_))
          (Finset.coe_inter _ _)⟩
      · rw [Finset.mem_inter] at he'
        obtain ⟨u₁, hu₁, hev₁⟩ := hYX e' he'.1
        obtain ⟨u₂, hu₂, hev₂⟩ := hYY e' he'.2
        have h₁ : u₁ ∈ X := by exact_mod_cast hu₁
        have h₂ : u₂ ∈ Y := by exact_mod_cast hu₂
        exact ⟨u₁, hmemZ h₁ ((hpair h₁ h₂).1 e' hev₁ hev₂ ▸ h₂), hev₁⟩
      · rintro v ((hv | hv) | hv)
        · obtain ⟨u, hu, hev⟩ := hYX v hv
          exact ⟨u, Or.inl (Or.inl hu), hev⟩
        · obtain ⟨u, hu, hev⟩ := hYY v hv
          exact ⟨u, Or.inl (Or.inr hu), hev⟩
        · exact ⟨t, Or.inr rfl, (Set.mem_singleton_iff.mp hv) ▸ he⟩
    · rintro f hf
      obtain ⟨YX, hYX, henX⟩ := hX.2 f hf
      obtain ⟨YY, hYY, henY⟩ := hY.2 f hf
      refine ⟨YX ∩ YY, fun f' hf' => ?_,
        F.enable_inter henX henY (fun V hV => con_projR hcons V (hV.trans ?_))
          (Finset.coe_inter _ _)⟩
      · rw [Finset.mem_inter] at hf'
        obtain ⟨u₁, hu₁, hev₁⟩ := hYX f' hf'.1
        obtain ⟨u₂, hu₂, hev₂⟩ := hYY f' hf'.2
        have h₁ : u₁ ∈ X := by exact_mod_cast hu₁
        have h₂ : u₂ ∈ Y := by exact_mod_cast hu₂
        exact ⟨u₁, hmemZ h₁ ((hpair h₁ h₂).2 f' hev₁ hev₂ ▸ h₂), hev₁⟩
      · rintro v ((hv | hv) | hv)
        · obtain ⟨u, hu, hev⟩ := hYX v hv
          exact ⟨u, Or.inl (Or.inl hu), hev⟩
        · obtain ⟨u, hu, hev⟩ := hYY v hv
          exact ⟨u, Or.inl (Or.inr hu), hev⟩
        · exact ⟨t, Or.inr rfl, (Set.mem_singleton_iff.mp hv) ▸ hf⟩

/-! ## Projections and steps -/

variable {c : Set (Tag E F)}

lemma projL_eq_pmap (c : Set (Tag E F)) :
    projL c = GES.pmapSet (G := (parSES E F).toGES) (H := E.toGES) Tag.evL c := rfl

lemma projR_eq_pmap (c : Set (Tag E F)) :
    projR c = GES.pmapSet (G := (parSES E F).toGES) (H := F.toGES) Tag.evR c := rfl

/-- The left projection of a configuration is a configuration. -/
lemma projL_isConf (hc : (parSES E F).toGES.isConf c) : E.toGES.isConf (projL c) :=
  GES.isConf_pmap (G := (parSES E F).toGES) (H := E.toGES) Tag.evL
    (fun {s} h => con_projL (s := s) h)
    (fun {_ _ x} hX hu => (hX.1 x hu)) hc

lemma projR_isConf (hc : (parSES E F).toGES.isConf c) : F.toGES.isConf (projR c) :=
  GES.isConf_pmap (G := (parSES E F).toGES) (H := F.toGES) Tag.evR
    (fun {s} h => con_projR (s := s) h)
    (fun {_ _ x} hX hu => (hX.2 x hu)) hc

lemma projL_insert {t : Tag E F} {x : E.Event} (hx : t.evL = some x) :
    projL (c ∪ {t}) = projL c ∪ {x} := by
  ext e
  constructor
  · rintro ⟨u, hu | hu, he⟩
    · exact Or.inl ⟨u, hu, he⟩
    · replace hu : u = t := hu
      subst hu
      rw [hx] at he
      exact Or.inr (Option.some.inj he).symm
  · rintro (⟨u, hu, he⟩ | he)
    · exact ⟨u, Or.inl hu, he⟩
    · replace he : e = x := he
      exact ⟨t, Or.inr rfl, by rw [hx, he]⟩

lemma projL_insert_none {t : Tag E F} (hx : t.evL = none) :
    projL (c ∪ {t}) = projL c := by
  ext e
  constructor
  · rintro ⟨u, hu | hu, he⟩
    · exact ⟨u, hu, he⟩
    · replace hu : u = t := hu
      subst hu
      rw [hx] at he
      exact absurd he (by simp)
  · rintro ⟨u, hu, he⟩
    exact ⟨u, Or.inl hu, he⟩

lemma projR_insert {t : Tag E F} {y : F.Event} (hy : t.evR = some y) :
    projR (c ∪ {t}) = projR c ∪ {y} := by
  ext f
  constructor
  · rintro ⟨u, hu | hu, he⟩
    · exact Or.inl ⟨u, hu, he⟩
    · replace hu : u = t := hu
      subst hu
      rw [hy] at he
      exact Or.inr (Option.some.inj he).symm
  · rintro (⟨u, hu, he⟩ | he)
    · exact ⟨u, Or.inl hu, he⟩
    · replace he : f = y := he
      exact ⟨t, Or.inr rfl, by rw [hy, he]⟩

lemma projR_insert_none {t : Tag E F} (hy : t.evR = none) :
    projR (c ∪ {t}) = projR c := by
  ext f
  constructor
  · rintro ⟨u, hu | hu, he⟩
    · exact ⟨u, hu, he⟩
    · replace hu : u = t := hu
      subst hu
      rw [hy] at he
      exact absurd he (by simp)
  · rintro ⟨u, hu, he⟩
    exact ⟨u, Or.inl hu, he⟩

/-- Firing a tag fires an enabled, fresh event of each component it consumes. -/
lemma enables_projL {t : Tag E F} {x : E.Event}
    (hins : (parSES E F).toGES.isConf (c ∪ {t}))
    (hfr : t ∉ c) (hx : t.evL = some x) :
    E.toGES.isConf (projL c ∪ {x}) ∧ x ∉ projL c := by
  refine ⟨(projL_insert hx) ▸ projL_isConf hins, ?_⟩
  rintro ⟨u, hu, hev⟩
  refine hfr ?_
  classical
  have hpair : ParCon ({u, t} : Finset (Tag E F)) := by
    refine hins.1 {u, t} fun v hv => ?_
    rcases Finset.mem_insert.mp (by exact_mod_cast hv) with rfl | hv'
    · exact Or.inl hu
    · exact (Finset.mem_singleton.mp hv') ▸ Or.inr rfl
  have : u = t :=
    (hpair.1 u (Finset.mem_insert_self _ _) t
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))).1 x hev hx
  exact this ▸ hu

lemma enables_projR {t : Tag E F} {y : F.Event}
    (hins : (parSES E F).toGES.isConf (c ∪ {t}))
    (hfr : t ∉ c) (hy : t.evR = some y) :
    F.toGES.isConf (projR c ∪ {y}) ∧ y ∉ projR c := by
  refine ⟨(projR_insert hy) ▸ projR_isConf hins, ?_⟩
  rintro ⟨u, hu, hev⟩
  refine hfr ?_
  classical
  have hpair : ParCon ({u, t} : Finset (Tag E F)) := by
    refine hins.1 {u, t} fun v hv => ?_
    rcases Finset.mem_insert.mp (by exact_mod_cast hv) with rfl | hv'
    · exact Or.inl hu
    · exact (Finset.mem_singleton.mp hv') ▸ Or.inr rfl
  have : u = t :=
    (hpair.1 u (Finset.mem_insert_self _ _) t
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))).2 y hev hy
  exact this ▸ hu

/-- A fresh tag whose components are enabled extends a configuration. -/
lemma isConf_insert_tag {t : Tag E F} (hc : (parSES E F).toGES.isConf c)
    (hL : ∀ x, t.evL = some x → E.toGES.isConf (projL c ∪ {x}) ∧ x ∉ projL c)
    (hR : ∀ y, t.evR = some y → F.toGES.isConf (projR c ∪ {y}) ∧ y ∉ projR c) :
    (parSES E F).toGES.isConf (c ∪ {t}) := by
  classical
  have hprojL : projL (c ∪ ({t} : Set (Tag E F))) = projL c ∪ {x | t.evL = some x} := by
    ext e
    constructor
    · rintro ⟨u, hu | hu, he⟩
      · exact Or.inl ⟨u, hu, he⟩
      · exact Or.inr ((Set.mem_singleton_iff.mp hu) ▸ he)
    · rintro (⟨u, hu, he⟩ | he)
      · exact ⟨u, Or.inl hu, he⟩
      · exact ⟨t, Or.inr rfl, he⟩
  have hprojR : projR (c ∪ ({t} : Set (Tag E F))) = projR c ∪ {y | t.evR = some y} := by
    ext f
    constructor
    · rintro ⟨u, hu | hu, he⟩
      · exact Or.inl ⟨u, hu, he⟩
      · exact Or.inr ((Set.mem_singleton_iff.mp hu) ▸ he)
    · rintro (⟨u, hu, he⟩ | he)
      · exact ⟨u, Or.inl hu, he⟩
      · exact ⟨t, Or.inr rfl, he⟩
  -- consistency
  have hconL : E.toGES.Consistent (projL (c ∪ ({t} : Set (Tag E F)))) := by
    rw [hprojL]
    cases hev : t.evL with
    | none =>
      have : {x | (none : Option E.Event) = some x} = (∅ : Set E.Event) := by ext e; simp
      rw [this, Set.union_empty]
      exact (projL_isConf hc).1
    | some x =>
      have : {z | (some x : Option E.Event) = some z} = ({x} : Set E.Event) := by
        ext z; simp [eq_comm]
      rw [this]
      exact (hL x hev).1.1
  have hconR : F.toGES.Consistent (projR (c ∪ ({t} : Set (Tag E F)))) := by
    rw [hprojR]
    cases hev : t.evR with
    | none =>
      have : {y | (none : Option F.Event) = some y} = (∅ : Set F.Event) := by ext f; simp
      rw [this, Set.union_empty]
      exact (projR_isConf hc).1
    | some y =>
      have : {z | (some y : Option F.Event) = some z} = ({y} : Set F.Event) := by
        ext z; simp [eq_comm]
      rw [this]
      exact (hR y hev).1.1
  refine ⟨fun W hW => ⟨fun t₁ h₁ t₂ h₂ => ⟨fun e he₁ he₂ => ?_, fun f hf₁ hf₂ => ?_⟩,
    fun V hV => hconL V (hV.trans (projL_mono hW)),
    fun V hV => hconR V (hV.trans (projR_mono hW))⟩, ?_⟩
  · -- injectivity on the left
    rcases hW (by exact_mod_cast h₁) with hm₁ | hm₁ <;>
      rcases hW (by exact_mod_cast h₂) with hm₂ | hm₂
    · exact (hc.1 {t₁, t₂} (by
        intro u hu
        rcases Finset.mem_insert.mp (by exact_mod_cast hu) with rfl | hu'
        · exact hm₁
        · exact (Finset.mem_singleton.mp hu') ▸ hm₂)).1 t₁ (Finset.mem_insert_self _ _) t₂
          (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) |>.1 e he₁ he₂
    · exact absurd ⟨t₁, hm₁, he₁⟩ ((hL e ((Set.mem_singleton_iff.mp hm₂) ▸ he₂)).2)
    · exact absurd ⟨t₂, hm₂, he₂⟩ ((hL e ((Set.mem_singleton_iff.mp hm₁) ▸ he₁)).2)
    · rw [Set.mem_singleton_iff] at hm₁ hm₂; rw [hm₁, hm₂]
  · -- injectivity on the right
    rcases hW (by exact_mod_cast h₁) with hm₁ | hm₁ <;>
      rcases hW (by exact_mod_cast h₂) with hm₂ | hm₂
    · exact (hc.1 {t₁, t₂} (by
        intro u hu
        rcases Finset.mem_insert.mp (by exact_mod_cast hu) with rfl | hu'
        · exact hm₁
        · exact (Finset.mem_singleton.mp hu') ▸ hm₂)).1 t₁ (Finset.mem_insert_self _ _) t₂
          (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) |>.2 f hf₁ hf₂
    · exact absurd ⟨t₁, hm₁, hf₁⟩ ((hR f ((Set.mem_singleton_iff.mp hm₂) ▸ hf₂)).2)
    · exact absurd ⟨t₂, hm₂, hf₂⟩ ((hR f ((Set.mem_singleton_iff.mp hm₁) ▸ hf₁)).2)
    · rw [Set.mem_singleton_iff] at hm₁ hm₂; rw [hm₁, hm₂]
  · -- securedness
    have hmono : ∀ {u : Tag E F}, u ∈ c →
        ∃ n, u ∈ (parSES E F).secApprox (c ∪ ({t} : Set (Tag E F))) n := by
      intro u hu
      obtain ⟨n, hn⟩ := hc.2 u hu
      exact ⟨n, GES.secApprox_mono_set Set.subset_union_left n hn⟩
    rintro u (hu | hu)
    · exact hmono hu
    · replace hu : u = t := hu
      subst hu
      -- cover each component's enabling set by tags of `c`
      obtain ⟨WL, hWLc, hWLen⟩ : ∃ W : Finset (Tag E F), ↑W ⊆ c ∧
          ∀ x, u.evL = some x → ∃ Y : Finset E.Event,
            (∀ e' ∈ Y, e' ∈ projL (W : Set (Tag E F))) ∧ E.enable Y x := by
        cases hev : u.evL with
        | none => exact ⟨∅, by simp, fun x hx => absurd hx (by simp)⟩
        | some x =>
          obtain ⟨k, hk⟩ : ∃ k, E.rank (projL c ∪ {x}) x = k + 1 := by
            have : E.rank (projL c ∪ {x}) x ≠ 0 := by
              intro h0
              have hmem := GES.rank_mem ((hL x hev).1.2 x (Or.inr rfl))
              rw [h0] at hmem
              exact hmem
            exact ⟨E.rank (projL c ∪ {x}) x - 1, by omega⟩
          obtain ⟨-, Y, hYsub, hYen⟩ := hk ▸ GES.rank_mem ((hL x hev).1.2 x (Or.inr rfl))
          have hYc : ↑Y ⊆ projL c := by
            intro y hy
            rcases GES.secApprox_subset _ (hYsub hy) with h | h
            · exact h
            · exact absurd (hk ▸ Nat.lt_succ_of_le (GES.rank_le (hYsub hy)) :
                E.rank (projL c ∪ {x}) y < E.rank (projL c ∪ {x}) x)
                (by rw [Set.mem_singleton_iff.mp h]; omega)
          obtain ⟨W, hWc, hWcov⟩ := exists_cover_L Y hYc
          exact ⟨W, hWc, fun x' hx' => ⟨Y, fun e' he' => hWcov (by exact_mod_cast he'),
            (Option.some.inj hx') ▸ hYen⟩⟩
      obtain ⟨WR, hWRc, hWRen⟩ : ∃ W : Finset (Tag E F), ↑W ⊆ c ∧
          ∀ y, u.evR = some y → ∃ Y : Finset F.Event,
            (∀ f' ∈ Y, f' ∈ projR (W : Set (Tag E F))) ∧ F.enable Y y := by
        cases hev : u.evR with
        | none => exact ⟨∅, by simp, fun y hy => absurd hy (by simp)⟩
        | some y =>
          obtain ⟨k, hk⟩ : ∃ k, F.rank (projR c ∪ {y}) y = k + 1 := by
            have : F.rank (projR c ∪ {y}) y ≠ 0 := by
              intro h0
              have hmem := GES.rank_mem ((hR y hev).1.2 y (Or.inr rfl))
              rw [h0] at hmem
              exact hmem
            exact ⟨F.rank (projR c ∪ {y}) y - 1, by omega⟩
          obtain ⟨-, Y, hYsub, hYen⟩ := hk ▸ GES.rank_mem ((hR y hev).1.2 y (Or.inr rfl))
          have hYc : ↑Y ⊆ projR c := by
            intro z hz
            rcases GES.secApprox_subset _ (hYsub hz) with h | h
            · exact h
            · exact absurd (hk ▸ Nat.lt_succ_of_le (GES.rank_le (hYsub hz)) :
                F.rank (projR c ∪ {y}) z < F.rank (projR c ∪ {y}) y)
                (by rw [Set.mem_singleton_iff.mp h]; omega)
          obtain ⟨W, hWc, hWcov⟩ := exists_cover_R Y hYc
          exact ⟨W, hWc, fun y' hy' => ⟨Y, fun f' hf' => hWcov (by exact_mod_cast hf'),
            (Option.some.inj hy') ▸ hYen⟩⟩
      obtain ⟨N, hN⟩ := GES.exists_bound (G := (parSES E F).toGES) (X := WL ∪ WR)
        fun g hg => by
          rcases Finset.mem_union.mp hg with h | h
          · exact hmono (hWLc (by exact_mod_cast h))
          · exact hmono (hWRc (by exact_mod_cast h))
      refine ⟨N + 1, Or.inr rfl, WL ∪ WR, hN, fun x hx => ?_, fun y hy => ?_⟩
      · exact (hWLen x hx).imp fun _ hY =>
          ⟨fun e' he' => projL_mono (by exact_mod_cast Finset.subset_union_left)
            (hY.1 e' he'), hY.2⟩
      · exact (hWRen y hy).imp fun _ hY =>
          ⟨fun f' hf' => projR_mono (by exact_mod_cast Finset.subset_union_right)
            (hY.1 f' hf'), hY.2⟩

end CCS
