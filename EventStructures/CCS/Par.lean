import EventStructures.Prime.Basic
import EventStructures.Prime.Configuration
import EventStructures.CCS.Syntax
import Mathlib.Logic.Relation
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Set.Card

/-! # Parallel composition of event structures

The product of prime event structures is stable, not prime.

An event is therefore a *prime state* — a set of tags carrying its own causal
history, with a unique maximal tag and least among states containing it, and
`Secured` to exclude deadlocked histories. Order is history inclusion; conflict
is failure to merge. -/

open PES Configuration

namespace CCS

variable {Name : Type*}

/-- A product event: an `E`-event, an `F`-event, or a label-matched synchronisation. -/
inductive Tag (E F : PES (Action Name)) where
  | left : E.Event → Tag E F
  | right : F.Event → Tag E F
  | sync (e : E.Event) (f : F.Event)
      (h : ∃ a, E.label e = .vis a ∧ F.label f = .vis a.co) : Tag E F

namespace Tag

variable {E F : PES (Action Name)}

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

variable {E F : PES (Action Name)}

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

/-- Each component event consumed once; both projections configurations. -/
def IsState (C : Set (Tag E F)) : Prop :=
  (∀ t ∈ C, ∀ t' ∈ C, ∀ e, t.evL = some e → t'.evL = some e → t = t') ∧
  (∀ t ∈ C, ∀ t' ∈ C, ∀ f, t.evR = some f → t'.evR = some f → t = t') ∧
  isConf E (projL C) ∧ isConf F (projR C)

lemma IsState.downL {C : Set (Tag E F)} (h : IsState C) {e e' : E.Event}
    (he : e ∈ projL C) (hle : e' ≤ e) : e' ∈ projL C := h.2.2.1.2 he hle

lemma IsState.downR {C : Set (Tag E F)} (h : IsState C) {f f' : F.Event}
    (hf : f ∈ projR C) (hle : f' ≤ f) : f' ∈ projR C := h.2.2.2.2 hf hle

/-- A subset of a state whose projections stay downward closed is a state. -/
lemma isState_of_subset {C D : Set (Tag E F)} (hC : IsState C) (hsub : D ⊆ C)
    (hL : ∀ {e e' : E.Event}, e ∈ projL D → e' ≤ e → e' ∈ projL D)
    (hR : ∀ {f f' : F.Event}, f ∈ projR D → f' ≤ f → f' ∈ projR D) : IsState D :=
  ⟨fun t ht t' ht' e h1 h2 => hC.1 t (hsub ht) t' (hsub ht') e h1 h2,
   fun t ht t' ht' f h1 h2 => hC.2.1 t (hsub ht) t' (hsub ht') f h1 h2,
   ⟨fun h1 h2 => hC.2.2.1.1 (projL_mono hsub h1) (projL_mono hsub h2), hL⟩,
   ⟨fun h1 h2 => hC.2.2.2.1 (projR_mono hsub h1) (projR_mono hsub h2), hR⟩⟩

/-- Reachable states: built one tag at a time. Downward closure alone admits
deadlocks like `{sync e₁ f₁, sync e₂ f₂}` with `e₁ < e₂` and `f₂ < f₁`. -/
inductive Secured : Set (Tag E F) → Prop
  | empty : Secured ∅
  | step {C : Set (Tag E F)} {t : Tag E F} :
      Secured C → t ∉ C → IsState (insert t C) → Secured (insert t C)

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

lemma isState_empty : IsState (∅ : Set (Tag E F)) := by
  refine ⟨fun t ht => (Set.notMem_empty t ht).elim,
          fun t ht => (Set.notMem_empty t ht).elim, ?_, ?_⟩
  · rw [projL_empty]
    exact ⟨fun h _ _ => (Set.notMem_empty _ h).elim, fun h _ => (Set.notMem_empty _ h).elim⟩
  · rw [projR_empty]
    exact ⟨fun h _ _ => (Set.notMem_empty _ h).elim, fun h _ => (Set.notMem_empty _ h).elim⟩

/-- `insert t C \ {t} = C` for fresh `t`, without deciding membership. -/
lemma insert_diff_self {C : Set (Tag E F)} {t : Tag E F} (h : t ∉ C) :
    insert t C \ {t} = C := by
  ext x
  constructor
  · rintro ⟨hx | hx, hne⟩
    · exact absurd hx hne
    · exact hx
  · exact fun hx => ⟨Or.inr hx, fun he => h (he ▸ hx)⟩

lemma Secured.isState {C : Set (Tag E F)} : Secured C → IsState C
  | .empty => isState_empty
  | .step _ _ h => h

/-- A nonempty secured state has a removable tag: the last inserted. -/
lemma Secured.exists_max {C : Set (Tag E F)} (h : Secured C) :
    C.Nonempty → ∃ t ∈ C, IsState (C \ {t}) := by
  induction h with
  | empty => rintro ⟨x, hx⟩; exact absurd hx (Set.notMem_empty x)
  | @step C t hC hnew _ _ =>
    exact fun _ => ⟨t, Set.mem_insert _ _, by
      rw [insert_diff_self hnew]; exact hC.isState⟩

/-- Events of `E ∥ F`: a tag together with its causal history. -/
structure ParEvent (E F : PES (Action Name)) where
  /-- The causal history, including the event itself. -/
  hist : Set (Tag E F)
  /-- The event proper: the unique maximal tag of `hist`. -/
  top : Tag E F
  state : IsState hist
  secured : Secured hist
  top_mem : top ∈ hist
  /-- The history is the *least* state containing the event. -/
  hist_min : ∀ D ⊆ hist, IsState D → top ∈ D → D = hist

namespace ParEvent

variable {E F : PES (Action Name)}

/-- Only the top is removable. -/
lemma top_uniq (p : ParEvent E F) {t : Tag E F} (ht : t ∈ p.hist)
    (hst : IsState (p.hist \ {t})) : t = p.top := by
  by_contra hne
  have htop : p.top ∈ p.hist \ {t} :=
    ⟨p.top_mem, fun h => hne (Set.mem_singleton_iff.mp h).symm⟩
  have := p.hist_min _ Set.diff_subset hst htop
  exact (this ▸ ht).2 rfl

lemma top_max (p : ParEvent E F) : IsState (p.hist \ {p.top}) := by
  obtain ⟨u, hu, hst⟩ := p.secured.exists_max ⟨p.top, p.top_mem⟩
  exact (p.top_uniq hu hst) ▸ hst

lemma ext' {p q : ParEvent E F} (h : p.hist = q.hist) : p = q := by
  have htop : p.top = q.top :=
    q.top_uniq (h ▸ p.top_mem) (by rw [← h]; exact p.top_max)
  cases p; cases q; cases h; cases htop; rfl

/-- Unions of histories have downward closed left projection. -/
lemma union_downL (p q : ParEvent E F) {e e' : E.Event}
    (he : e ∈ projL (p.hist ∪ q.hist)) (hle : e' ≤ e) :
    e' ∈ projL (p.hist ∪ q.hist) := by
  rw [projL_union] at he ⊢
  rcases he with h | h
  · exact Or.inl (p.state.downL h hle)
  · exact Or.inr (q.state.downL h hle)

/-- Unions of histories have downward closed right projection. -/
lemma union_downR (p q : ParEvent E F) {f f' : F.Event}
    (hf : f ∈ projR (p.hist ∪ q.hist)) (hle : f' ≤ f) :
    f' ∈ projR (p.hist ∪ q.hist) := by
  rw [projR_union] at hf ⊢
  rcases hf with h | h
  · exact Or.inl (p.state.downR h hle)
  · exact Or.inr (q.state.downR h hle)

lemma hist_nonempty (p : ParEvent E F) : p.hist.Nonempty := ⟨p.top, p.top_mem⟩

end ParEvent

/-- A tag with minimal components is a state on its own. -/
lemma isState_singleton (t : Tag E F)
    (hL : ∀ {e e' : E.Event}, t.evL = some e → e' ≤ e → e' = e)
    (hR : ∀ {f f' : F.Event}, t.evR = some f → f' ≤ f → f' = f) :
    IsState ({t} : Set (Tag E F)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha b hb _ _ _
    rw [Set.mem_singleton_iff] at ha hb; rw [ha, hb]
  · intro a ha b hb _ _ _
    rw [Set.mem_singleton_iff] at ha hb; rw [ha, hb]
  · rw [projL_singleton]
    refine ⟨?_, ?_⟩
    · intro e₁ e₂ h1 h2
      simp only [Set.mem_setOf_eq] at h1 h2
      rw [h1] at h2
      exact Option.some.inj h2 ▸ E.conflict_irrefl _
    · intro e e' he hle
      simp only [Set.mem_setOf_eq] at he ⊢
      exact hL he hle ▸ he
  · rw [projR_singleton]
    refine ⟨?_, ?_⟩
    · intro f₁ f₂ h1 h2
      simp only [Set.mem_setOf_eq] at h1 h2
      rw [h1] at h2
      exact Option.some.inj h2 ▸ F.conflict_irrefl _
    · intro f f' hf hle
      simp only [Set.mem_setOf_eq] at hf ⊢
      exact hR hf hle ▸ hf

lemma secured_singleton {t : Tag E F} (h : IsState ({t} : Set (Tag E F))) :
    Secured ({t} : Set (Tag E F)) := by
  have hins : ({t} : Set (Tag E F)) = insert t ∅ := by simp
  rw [hins]
  exact Secured.step Secured.empty (Set.notMem_empty t) (hins ▸ h)

/-- A tag with minimal components is a prime state on its own. -/
def minTagEvent (t : Tag E F)
    (hL : ∀ {e e' : E.Event}, t.evL = some e → e' ≤ e → e' = e)
    (hR : ∀ {f f' : F.Event}, t.evR = some f → f' ≤ f → f' = f) : ParEvent E F where
  hist := {t}
  top := t
  state := isState_singleton t hL hR
  secured := secured_singleton (isState_singleton t hL hR)
  top_mem := rfl
  hist_min := fun _ hD _ ht => Set.Subset.antisymm hD (Set.singleton_subset_iff.mpr ht)

/-- Parallel composition: events are prime states, ordered by history inclusion,
in conflict when their histories cannot be merged. -/
def par (E F : PES (Action Name)) : PES (Action Name) where
  Event := ParEvent E F
  poEvent :=
    { le := fun p q => p.hist ⊆ q.hist
      lt := fun p q => p.hist ⊆ q.hist ∧ ¬ q.hist ⊆ p.hist
      le_refl := fun _ => Set.Subset.refl _
      le_trans := fun _ _ _ h h' => Set.Subset.trans h h'
      le_antisymm := fun _ _ h h' => ParEvent.ext' (Set.Subset.antisymm h h')
      lt_iff_le_not_ge := fun _ _ => Iff.rfl }
  conflict := fun p q => ¬ IsState (p.hist ∪ q.hist)
  label := fun p => p.top.label
  conflict_irrefl := fun p h => h (by rw [Set.union_self]; exact p.state)
  conflict_symm := fun _ _ h hst => h (by rw [Set.union_comm]; exact hst)
  conflict_hereditary := fun {p q r} hpq hqr hpr =>
    hpq (isState_of_subset hpr (Set.union_subset_union_right _ hqr)
          (ParEvent.union_downL p q) (ParEvent.union_downR p q))

/-- A singleton history is minimal, hence enabled at the empty configuration. -/
lemma enables_minTagEvent (t : Tag E F)
    (hL : ∀ {e e' : E.Event}, t.evL = some e → e' ≤ e → e' = e)
    (hR : ∀ {f f' : F.Event}, t.evR = some f → f' ≤ f → f' = f) :
    Configuration.enables (par E F) ∅ (minTagEvent t hL hR) := by
  refine ⟨⟨fun h _ _ => (Set.notMem_empty _ h).elim,
           fun h _ => (Set.notMem_empty _ h).elim⟩,
          fun _ h => (Set.notMem_empty _ h).elim, ?_⟩
  rintro q ⟨hsub, hnsub⟩
  refine absurd (fun x hx => ?_) hnsub
  have hx' : x = t := hx
  have htop : q.top = t := hsub q.top_mem
  rw [hx']
  exact htop ▸ q.top_mem



/-! ## Causal histories

Every tag of a secured state is the top of a unique least substate —
its causal history. -/

/-- One-step causal dependency: two tags sharing a component, ordered. -/
def TagLe (t' t : Tag E F) : Prop :=
  (∃ x' x, t'.evL = some x' ∧ t.evL = some x ∧ x' ≤ x) ∨
  (∃ f' f, t'.evR = some f' ∧ t.evR = some f ∧ f' ≤ f)

/-- Causal dependency chains inside a set of tags. -/
def Dep (S : Set (Tag E F)) : Tag E F → Tag E F → Prop :=
  Relation.ReflTransGen (fun a b => a ∈ S ∧ b ∈ S ∧ TagLe a b)

/-- The causal history of `t` inside `S`. -/
def dc (S : Set (Tag E F)) (t : Tag E F) : Set (Tag E F) := {t' | t' ∈ S ∧ Dep S t' t}

lemma dc_subset {S : Set (Tag E F)} {t : Tag E F} : dc S t ⊆ S := fun _ h => h.1

lemma dc_self {S : Set (Tag E F)} {t : Tag E F} (ht : t ∈ S) : t ∈ dc S t :=
  ⟨ht, Relation.ReflTransGen.refl⟩

/-- Any state inside `S` containing `t` already contains the whole history of `t`. -/
lemma dc_least {S D : Set (Tag E F)} {t : Tag E F} (hS : IsState S) (hD : IsState D)
    (hDS : D ⊆ S) (ht : t ∈ D) : dc S t ⊆ D := by
  rintro t' ⟨-, hdep⟩
  induction hdep using Relation.ReflTransGen.head_induction_on with
  | refl => exact ht
  | head hstep _ ih =>
    obtain ⟨haS, -, hle⟩ := hstep
    rcases hle with ⟨x', x, hx', hx, hxle⟩ | ⟨f', f, hf', hf, hfle⟩
    · obtain ⟨w, hwD, hw⟩ := hD.downL (⟨_, ih, hx⟩ : x ∈ projL D) hxle
      exact hS.1 w (hDS hwD) _ haS x' hw hx' ▸ hwD
    · obtain ⟨w, hwD, hw⟩ := hD.downR (⟨_, ih, hf⟩ : f ∈ projR D) hfle
      exact hS.2.1 w (hDS hwD) _ haS f' hw hf' ▸ hwD

lemma isState_dc {S : Set (Tag E F)} (hS : IsState S) (t : Tag E F) : IsState (dc S t) := by
  refine isState_of_subset hS dc_subset ?_ ?_
  · rintro x x' ⟨w, ⟨hwS, hwdep⟩, hw⟩ hle
    obtain ⟨v, hvS, hv⟩ := hS.downL (⟨w, hwS, hw⟩ : x ∈ projL S) hle
    exact ⟨v, ⟨hvS, .head ⟨hvS, hwS, Or.inl ⟨x', x, hv, hw, hle⟩⟩ hwdep⟩, hv⟩
  · rintro f f' ⟨w, ⟨hwS, hwdep⟩, hw⟩ hle
    obtain ⟨v, hvS, hv⟩ := hS.downR (⟨w, hwS, hw⟩ : f ∈ projR S) hle
    exact ⟨v, ⟨hvS, .head ⟨hvS, hwS, Or.inr ⟨f', f, hv, hw, hle⟩⟩ hwdep⟩, hv⟩

/-- A freshly inserted tag depends on nothing already present. -/
lemma not_TagLe_fresh {C : Set (Tag E F)} {u v : Tag E F}
    (hins : IsState (insert u C)) (hC : IsState C) (hu : u ∉ C) (hv : v ∈ C) :
    ¬ TagLe u v := by
  rintro (⟨x, x', hx, hx', hle⟩ | ⟨f, f', hf, hf', hle⟩)
  · obtain ⟨w, hwC, hw⟩ := hC.downL (⟨v, hv, hx'⟩ : x' ∈ projL C) hle
    exact hu ((hins.1 u (Set.mem_insert _ _) w (Set.mem_insert_of_mem _ hwC) x hx hw) ▸ hwC)
  · obtain ⟨w, hwC, hw⟩ := hC.downR (⟨v, hv, hf'⟩ : f' ∈ projR C) hle
    exact hu ((hins.2.1 u (Set.mem_insert _ _) w (Set.mem_insert_of_mem _ hwC) f hf hw) ▸ hwC)

/-- Substates closed under causal predecessors inherit securedness. -/
lemma secured_of_closed {S : Set (Tag E F)} (hS : Secured S) :
    ∀ {D : Set (Tag E F)}, D ⊆ S → IsState D →
      (∀ a ∈ D, ∀ b ∈ S, TagLe b a → b ∈ D) → Secured D := by
  induction hS with
  | empty =>
    intro D hDS _ _
    exact (Set.subset_empty_iff.mp hDS) ▸ Secured.empty
  | @step C u hC huC hins ih =>
    intro D hDS hD hclosed
    by_cases huD : u ∈ D
    · have hsub : D \ {u} ⊆ C := by
        rintro v ⟨hvD, hvu⟩
        rcases hDS hvD with rfl | hvC
        · exact absurd rfl hvu
        · exact hvC
      have hDu : IsState (D \ {u}) := by
        refine isState_of_subset hD Set.diff_subset ?_ ?_
        · rintro x x' ⟨w, ⟨hwD, hwu⟩, hw⟩ hle
          obtain ⟨v, hvD, hv⟩ := hD.downL (⟨w, hwD, hw⟩ : x ∈ projL D) hle
          refine ⟨v, ⟨hvD, ?_⟩, hv⟩
          rintro rfl
          exact not_TagLe_fresh hins hC.isState huC (hsub ⟨hwD, hwu⟩)
            (Or.inl ⟨x', x, hv, hw, hle⟩)
        · rintro f f' ⟨w, ⟨hwD, hwu⟩, hw⟩ hle
          obtain ⟨v, hvD, hv⟩ := hD.downR (⟨w, hwD, hw⟩ : f ∈ projR D) hle
          refine ⟨v, ⟨hvD, ?_⟩, hv⟩
          rintro rfl
          exact not_TagLe_fresh hins hC.isState huC (hsub ⟨hwD, hwu⟩)
            (Or.inr ⟨f', f, hv, hw, hle⟩)
      have hsec : Secured (D \ {u}) :=
        ih hsub hDu (fun a ha b hb hlt =>
          ⟨hclosed a ha.1 b (Set.mem_insert_of_mem _ hb) hlt, fun hbu =>
            huC ((Set.mem_singleton_iff.mp hbu) ▸ hb)⟩)
      have heq : insert u (D \ {u}) = D := by
        rw [Set.insert_diff_singleton, Set.insert_eq_self.mpr huD]
      have hD' : IsState (insert u (D \ {u})) := by rw [heq]; exact hD
      rw [← heq]
      exact Secured.step hsec (fun h => h.2 rfl) hD'
    · refine ih (fun v hv => ?_) hD
        (fun a ha b hb hlt => hclosed a ha b (Set.mem_insert_of_mem _ hb) hlt)
      rcases hDS hv with rfl | h
      · exact absurd hv huD
      · exact h

lemma secured_dc {S : Set (Tag E F)} (hS : Secured S) (t : Tag E F) : Secured (dc S t) :=
  secured_of_closed hS dc_subset (isState_dc hS.isState t)
    (fun _ ha _ hb hlt => ⟨hb, .head ⟨hb, ha.1, hlt⟩ ha.2⟩)

/-- Only `t` itself can be removed from its own history. -/
lemma dc_top_uniq {S : Set (Tag E F)} (hS : IsState S) {t : Tag E F} (ht : t ∈ S)
    {u : Tag E F} (hu : u ∈ dc S t) (hst : IsState (dc S t \ {u})) : u = t := by
  by_contra hne
  have htmem : t ∈ dc S t \ {u} :=
    ⟨dc_self ht, fun h => hne (Set.mem_singleton_iff.mp h).symm⟩
  exact (dc_least hS hst (fun v hv => dc_subset hv.1) htmem hu).2 rfl

/-- The prime event with top `t` inside a secured state. -/
def primeOf {S : Set (Tag E F)} (hS : Secured S) {t : Tag E F} (ht : t ∈ S) : ParEvent E F where
  hist := dc S t
  top := t
  state := isState_dc hS.isState t
  secured := secured_dc hS t
  top_mem := dc_self ht
  hist_min := fun _ hD hDst htD =>
    Set.Subset.antisymm hD
      (dc_least hS.isState hDst (fun _ hv => dc_subset (hD hv)) htD)

/-- Every non-top tag of a prime history is the top of a strictly smaller event. -/
lemma sub_event (q : ParEvent E F) {t : Tag E F} (ht : t ∈ q.hist) (hne : t ≠ q.top) :
    ∃ r : ParEvent E F, r.hist ⊆ q.hist ∧ r.hist ≠ q.hist ∧ r.top = t := by
  refine ⟨primeOf q.secured ht, dc_subset, ?_, rfl⟩
  intro heq
  exact hne (q.top_uniq ht (heq ▸ (primeOf q.secured ht).top_max))

/-! ## Configurations of `E ∥ F` -/

/-- The tags used by a set of events. -/
def flat (c : Set (ParEvent E F)) : Set (Tag E F) := {t | ∃ q ∈ c, t ∈ q.hist}

lemma mem_flat {c : Set (ParEvent E F)} {q : ParEvent E F} (hq : q ∈ c)
    {t : Tag E F} (ht : t ∈ q.hist) : t ∈ flat c := ⟨q, hq, ht⟩

lemma projL_flat {c : Set (ParEvent E F)} {x : E.Event} :
    x ∈ projL (flat c) ↔ ∃ q ∈ c, x ∈ projL q.hist := by
  constructor
  · rintro ⟨t, ⟨q, hq, ht⟩, hx⟩; exact ⟨q, hq, t, ht, hx⟩
  · rintro ⟨q, hq, t, ht, hx⟩; exact ⟨t, ⟨q, hq, ht⟩, hx⟩

lemma projR_flat {c : Set (ParEvent E F)} {y : F.Event} :
    y ∈ projR (flat c) ↔ ∃ q ∈ c, y ∈ projR q.hist := by
  constructor
  · rintro ⟨t, ⟨q, hq, ht⟩, hy⟩; exact ⟨q, hq, t, ht, hy⟩
  · rintro ⟨q, hq, t, ht, hy⟩; exact ⟨t, ⟨q, hq, ht⟩, hy⟩

/-- Compatible events merge: this is what conflict-freeness gives. -/
lemma isState_pair {p q : ParEvent E F} (h : ¬ (par E F).conflict p q) :
    IsState (p.hist ∪ q.hist) := not_not.mp h

/-- The tags of a configuration form a state. -/
lemma isState_flat {c : Set (ParEvent E F)} (hc : isConf (par E F) c) :
    IsState (flat c) := by
  refine ⟨?_, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rintro t ⟨q, hq, ht⟩ t' ⟨q', hq', ht'⟩ x hx hx'
    exact (isState_pair (hc.1 hq hq')).1 t (Or.inl ht) t' (Or.inr ht') x hx hx'
  · rintro t ⟨q, hq, ht⟩ t' ⟨q', hq', ht'⟩ y hy hy'
    exact (isState_pair (hc.1 hq hq')).2.1 t (Or.inl ht) t' (Or.inr ht') y hy hy'
  · rintro x x' hx hx'
    obtain ⟨q, hq, hxq⟩ := projL_flat.mp hx
    obtain ⟨q', hq', hxq'⟩ := projL_flat.mp hx'
    refine (isState_pair (hc.1 hq hq')).2.2.1.1 ?_ ?_ <;> rw [projL_union]
    · exact Or.inl hxq
    · exact Or.inr hxq'
  · rintro x x' hx hle
    obtain ⟨q, hq, hxq⟩ := projL_flat.mp hx
    exact projL_flat.mpr ⟨q, hq, q.state.downL hxq hle⟩
  · rintro y y' hy hy'
    obtain ⟨q, hq, hyq⟩ := projR_flat.mp hy
    obtain ⟨q', hq', hyq'⟩ := projR_flat.mp hy'
    refine (isState_pair (hc.1 hq hq')).2.2.2.1 ?_ ?_ <;> rw [projR_union]
    · exact Or.inl hyq
    · exact Or.inr hyq'
  · rintro y y' hy hle
    obtain ⟨q, hq, hyq⟩ := projR_flat.mp hy
    exact projR_flat.mpr ⟨q, hq, q.state.downR hyq hle⟩

/-- The past of an event covers all of its history but the top. -/
lemma hist_sub_flat {c : Set (ParEvent E F)} {q : ParEvent E F}
    (hpast : (par E F).past q ⊆ c) : q.hist \ {q.top} ⊆ flat c := by
  rintro t ⟨ht, hne⟩
  obtain ⟨r, hsub, hne', hrtop⟩ :=
    sub_event q ht (fun h => hne (Set.mem_singleton_iff.mpr h))
  refine mem_flat (hpast (?_ : r ∈ (par E F).past q)) (hrtop ▸ r.top_mem)
  exact ⟨hsub, fun h => hne' (Set.Subset.antisymm hsub h)⟩

/-- Adding an event adds exactly its top tag. -/
lemma flat_insert {c : Set (ParEvent E F)} {q : ParEvent E F}
    (hpast : (par E F).past q ⊆ c) : flat (c ∪ {q}) = insert q.top (flat c) := by
  ext t
  constructor
  · rintro ⟨r, hr | hr, ht⟩
    · exact Set.mem_insert_of_mem _ ⟨r, hr, ht⟩
    · rw [Set.mem_singleton_iff] at hr
      subst hr
      by_cases htt : t = r.top
      · exact htt ▸ Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ (hist_sub_flat hpast ⟨ht, htt⟩)
  · rintro (rfl | ⟨r, hr, ht⟩)
    · exact ⟨q, Or.inr rfl, q.top_mem⟩
    · exact ⟨r, Or.inl hr, ht⟩


/-- Secured states are listable: the securing sequence, positively. -/
lemma Secured.listable {C : Set (Tag E F)} (h : Secured C) :
    ∃ l : List (Tag E F), ∀ x, x ∈ C ↔ x ∈ l := by
  induction h with
  | empty =>
    refine ⟨[], fun x => ⟨fun hx => absurd hx (Set.notMem_empty x), fun hx => ?_⟩⟩
    exact absurd hx (List.not_mem_nil)
  | @step C t _ _ _ ih =>
    obtain ⟨l, hl⟩ := ih
    refine ⟨t :: l, fun x => ⟨?_, ?_⟩⟩
    · rintro (rfl | hx)
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ ((hl x).mp hx)
    · intro hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ ((hl x).mpr hx)

lemma Secured.finite {C : Set (Tag E F)} (h : Secured C) : C.Finite := by
  induction h with
  | empty => exact Set.finite_empty
  | step _ _ _ ih => exact ih.insert _

lemma flat_finite {c : Set (ParEvent E F)} (hfin : c.Finite) : (flat c).Finite := by
  have h : flat c = ⋃ q ∈ c, q.hist := by ext t; simp [flat]
  rw [h]
  exact hfin.biUnion (fun q _ => q.secured.finite)

lemma past_subset {c : Set (ParEvent E F)} (hc : isConf (par E F) c) {q : ParEvent E F}
    (hq : q ∈ c) : (par E F).past q ⊆ c \ {q} := by
  intro r hr
  refine ⟨hc.2 hq (le_of_lt hr), ?_⟩
  rintro hrq
  rw [Set.mem_singleton_iff] at hrq
  subst hrq
  exact absurd hr (lt_irrefl (α := (par E F).Event) r)

/-- The tags of a finite configuration form a secured state. -/
lemma secured_flat_aux : ∀ (n : ℕ) (c : Set (ParEvent E F)), c.Finite → c.ncard = n →
    isConf (par E F) c → Secured (flat c) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro c hfin hcard hc
    rcases Set.eq_empty_or_nonempty c with rfl | hne
    · have h : flat (∅ : Set (ParEvent E F)) = ∅ := by ext t; simp [flat]
      exact h ▸ Secured.empty
    obtain ⟨q, hqc, hmax⟩ := hfin.exists_maximalFor ParEvent.hist c hne
    have hsub : c \ {q} ⊆ c := Set.diff_subset
    have hpast : (par E F).past q ⊆ c \ {q} := past_subset hc hqc
    have hss : c \ {q} ⊂ c := Set.diff_singleton_ssubset.mpr hqc
    have hc'conf : isConf (par E F) (c \ {q}) := by
      refine ⟨fun h1 h2 => hc.1 (hsub h1) (hsub h2), ?_⟩
      intro r s hr hle
      refine ⟨hc.2 hr.1 hle, ?_⟩
      rintro hsq
      rw [Set.mem_singleton_iff] at hsq
      subst hsq
      exact hr.2 (Set.mem_singleton_iff.mpr
        (ParEvent.ext' (Set.Subset.antisymm hle (hmax hr.1 hle))).symm)
    have hflat : flat c = insert q.top (flat (c \ {q})) := by
      ext t
      constructor
      · rintro ⟨r, hr, ht⟩
        by_cases hrq : r = q
        · subst hrq
          by_cases htt : t = r.top
          · exact htt ▸ Set.mem_insert _ _
          · exact Set.mem_insert_of_mem _ (hist_sub_flat hpast ⟨ht, htt⟩)
        · exact Set.mem_insert_of_mem _
            ⟨r, ⟨hr, fun h => hrq (Set.mem_singleton_iff.mp h)⟩, ht⟩
      · rintro (rfl | ⟨r, hr, ht⟩)
        · exact ⟨q, hqc, q.top_mem⟩
        · exact ⟨r, hsub hr, ht⟩
    have htopfresh : q.top ∉ flat (c \ {q}) := by
      rintro ⟨r, ⟨hrc, hrq⟩, htop⟩
      have hM : IsState (q.hist ∪ r.hist) := isState_pair (hc.1 hqc hrc)
      have hle : q.hist ⊆ r.hist := by
        have h2 : dc (q.hist ∪ r.hist) q.top ⊆ r.hist :=
          dc_least hM r.state Set.subset_union_right htop
        have heq : dc (q.hist ∪ r.hist) q.top = q.hist :=
          q.hist_min _ (dc_least hM q.state Set.subset_union_left q.top_mem)
            (isState_dc hM _) (dc_self (Or.inl q.top_mem))
        exact heq ▸ h2
      exact hrq (Set.mem_singleton_iff.mpr
        (ParEvent.ext' (Set.Subset.antisymm hle (hmax hrc hle))).symm)
    rw [hflat]
    refine Secured.step (ih (c \ {q}).ncard ?_ (c \ {q}) (hfin.subset hsub) rfl hc'conf)
      htopfresh (hflat ▸ isState_flat hc)
    exact hcard ▸ Set.ncard_lt_ncard hss hfin

lemma secured_flat {c : Set (ParEvent E F)} (hfin : c.Finite) (hc : isConf (par E F) c) :
    Secured (flat c) := secured_flat_aux _ c hfin rfl hc

/-- A component of an enabled event is enabled on the projected configuration. -/
lemma comp_enables_L {c : Set (ParEvent E F)} {q : ParEvent E F} {x : E.Event}
    (hc : isConf (par E F) c) (hen : Configuration.enables (par E F) c q) (hfr : q ∉ c)
    (hx : q.top.evL = some x) :
    Configuration.enables E (projL (flat c)) x ∧ x ∉ projL (flat c) := by
  have hxq : x ∈ projL q.hist := ⟨q.top, q.top_mem, hx⟩
  have hcompat : ∀ q' ∈ c, IsState (q.hist ∪ q'.hist) :=
    fun q' hq' => isState_pair (hen.2.1 q' hq')
  refine ⟨⟨(isState_flat hc).2.2.1, ?_, ?_⟩, ?_⟩
  · rintro x' hx'
    obtain ⟨q', hq', hx'q⟩ := projL_flat.mp hx'
    refine (hcompat q' hq').2.2.1.1 ?_ ?_ <;> rw [projL_union]
    · exact Or.inl hxq
    · exact Or.inr hx'q
  · rintro x' hlt
    obtain ⟨t', ht', hx'⟩ := q.state.downL hxq (le_of_lt hlt)
    have hne : t' ≠ q.top := by
      rintro rfl
      rw [hx] at hx'
      exact absurd (Option.some.inj hx').symm (ne_of_lt hlt)
    exact ⟨t', hist_sub_flat hen.2.2 ⟨ht', fun h => hne (Set.mem_singleton_iff.mp h)⟩, hx'⟩
  · rintro hxflat
    obtain ⟨q', hq', t', ht', hxt'⟩ := projL_flat.mp hxflat
    have hM := hcompat q' hq'
    have htop : q.top = t' :=
      hM.1 q.top (Or.inl q.top_mem) t' (Or.inr ht') x hx hxt'
    have hdcq : dc (q.hist ∪ q'.hist) q.top ⊆ q.hist :=
      dc_least hM q.state Set.subset_union_left q.top_mem
    have hdcq' : dc (q.hist ∪ q'.hist) q.top ⊆ q'.hist :=
      dc_least hM q'.state Set.subset_union_right (htop ▸ ht')
    have heq : dc (q.hist ∪ q'.hist) q.top = q.hist :=
      q.hist_min _ hdcq (isState_dc hM _) (dc_self (Or.inl q.top_mem))
    have hle : q.hist ⊆ q'.hist := heq ▸ hdcq'
    exact hfr (hc.2 hq' hle)


lemma comp_enables_R {c : Set (ParEvent E F)} {q : ParEvent E F} {y : F.Event}
    (hc : isConf (par E F) c) (hen : Configuration.enables (par E F) c q) (hfr : q ∉ c)
    (hy : q.top.evR = some y) :
    Configuration.enables F (projR (flat c)) y ∧ y ∉ projR (flat c) := by
  have hyq : y ∈ projR q.hist := ⟨q.top, q.top_mem, hy⟩
  have hcompat : ∀ q' ∈ c, IsState (q.hist ∪ q'.hist) :=
    fun q' hq' => isState_pair (hen.2.1 q' hq')
  refine ⟨⟨(isState_flat hc).2.2.2, ?_, ?_⟩, ?_⟩
  · rintro y' hy'
    obtain ⟨q', hq', hy'q⟩ := projR_flat.mp hy'
    refine (hcompat q' hq').2.2.2.1 ?_ ?_ <;> rw [projR_union]
    · exact Or.inl hyq
    · exact Or.inr hy'q
  · rintro y' hlt
    obtain ⟨t', ht', hy'⟩ := q.state.downR hyq (le_of_lt hlt)
    have hne : t' ≠ q.top := by
      rintro rfl
      rw [hy] at hy'
      exact absurd (Option.some.inj hy').symm (ne_of_lt hlt)
    exact ⟨t', hist_sub_flat hen.2.2 ⟨ht', fun h => hne (Set.mem_singleton_iff.mp h)⟩, hy'⟩
  · rintro hyflat
    obtain ⟨q', hq', t', ht', hyt'⟩ := projR_flat.mp hyflat
    have hM := hcompat q' hq'
    have htop : q.top = t' :=
      hM.2.1 q.top (Or.inl q.top_mem) t' (Or.inr ht') y hy hyt'
    have hdcq : dc (q.hist ∪ q'.hist) q.top ⊆ q.hist :=
      dc_least hM q.state Set.subset_union_left q.top_mem
    have hdcq' : dc (q.hist ∪ q'.hist) q.top ⊆ q'.hist :=
      dc_least hM q'.state Set.subset_union_right (htop ▸ ht')
    have heq : dc (q.hist ∪ q'.hist) q.top = q.hist :=
      q.hist_min _ hdcq (isState_dc hM _) (dc_self (Or.inl q.top_mem))
    have hle : q.hist ⊆ q'.hist := heq ▸ hdcq'
    exact hfr (hc.2 hq' hle)

/-- Events below one built inside `insert t (flat c)` already live in `c`. -/
lemma past_of_primeOf {c : Set (ParEvent E F)} (hc : isConf (par E F) c)
    {t : Tag E F} {hS : Secured (insert t (flat c))}
    (q : ParEvent E F) (hq : q = primeOf hS (Set.mem_insert t (flat c))) :
    (par E F).past q ⊆ c := by
  rintro r hr
  have hrsub : r.hist ⊆ q.hist := hr.1
  have hrS : r.hist ⊆ insert t (flat c) := hrsub.trans (hq ▸ dc_subset)
  have hrdc : r.hist = dc (insert t (flat c)) r.top :=
    (r.hist_min _ (dc_least hS.isState r.state hrS r.top_mem)
      (isState_dc hS.isState _) (dc_self (hrS r.top_mem))).symm
  have hrtop : r.top ≠ t := by
    rintro rfl
    refine hr.2 ?_
    rw [hq]
    exact dc_least hS.isState r.state hrS r.top_mem
  obtain ⟨q'', hq'', ht''⟩ : ∃ q'' ∈ c, r.top ∈ q''.hist := by
    rcases hrS r.top_mem with h | h
    · exact absurd h hrtop
    · exact h
  have hle : r.hist ⊆ q''.hist := by
    rw [hrdc]
    exact (dc_least hS.isState (isState_dc q''.state r.top)
      ((dc_subset (S := q''.hist)).trans (fun v hv => Set.mem_insert_of_mem _ ⟨q'', hq'', hv⟩))
      (dc_self ht'')).trans dc_subset
  exact hc.2 hq'' hle


@[simp] lemma setOf_evL_left (x : E.Event) :
    {e | (Tag.left (F := F) x).evL = some e} = {x} := by ext e; simp [Tag.evL, eq_comm]
@[simp] lemma setOf_evR_left (x : E.Event) :
    {f | (Tag.left (F := F) x).evR = some f} = (∅ : Set F.Event) := by ext f; simp [Tag.evR]
@[simp] lemma setOf_evL_right (y : F.Event) :
    {e | (Tag.right (E := E) y).evL = some e} = (∅ : Set E.Event) := by ext e; simp [Tag.evL]
@[simp] lemma setOf_evR_right (y : F.Event) :
    {f | (Tag.right (E := E) y).evR = some f} = {y} := by ext f; simp [Tag.evR, eq_comm]
@[simp] lemma setOf_evL_sync (x : E.Event) (y : F.Event)
    (h : ∃ a, E.label x = .vis a ∧ F.label y = .vis a.co) :
    {e | (Tag.sync x y h).evL = some e} = {x} := by ext e; simp [Tag.evL, eq_comm]
@[simp] lemma setOf_evR_sync (x : E.Event) (y : F.Event)
    (h : ∃ a, E.label x = .vis a ∧ F.label y = .vis a.co) :
    {f | (Tag.sync x y h).evR = some f} = {y} := by ext f; simp [Tag.evR, eq_comm]

lemma projL_insert (t : Tag E F) (C : Set (Tag E F)) :
    projL (insert t C) = {e | t.evL = some e} ∪ projL C := by
  rw [Set.insert_eq, projL_union, projL_singleton]

lemma projR_insert (t : Tag E F) (C : Set (Tag E F)) :
    projR (insert t C) = {f | t.evR = some f} ∪ projR C := by
  rw [Set.insert_eq, projR_union, projR_singleton]

lemma projL_finite {C : Set (Tag E F)} (h : C.Finite) : (projL C).Finite := by
  have : projL C = ⋃ t ∈ C, {e | t.evL = some e} := by ext e; simp [projL]
  rw [this]
  refine h.biUnion (fun t _ => ?_)
  cases ht : t.evL with
  | none => simp
  | some x =>
    refine (Set.finite_singleton x).subset (fun e he => ?_)
    simp only [Set.mem_setOf_eq, Option.some.injEq] at he
    simp [he]

lemma projR_finite {C : Set (Tag E F)} (h : C.Finite) : (projR C).Finite := by
  have : projR C = ⋃ t ∈ C, {f | t.evR = some f} := by ext f; simp [projR]
  rw [this]
  refine h.biUnion (fun t _ => ?_)
  cases ht : t.evR with
  | none => simp
  | some y =>
    refine (Set.finite_singleton y).subset (fun f hf => ?_)
    simp only [Set.mem_setOf_eq, Option.some.injEq] at hf
    simp [hf]

/-- A tag with enabled components yields an enabled event. -/
lemma exists_event_tag {c : Set (ParEvent E F)} (hfin : c.Finite) (hc : isConf (par E F) c)
    (t : Tag E F)
    (hL : ∀ x, t.evL = some x →
      Configuration.enables E (projL (flat c)) x ∧ x ∉ projL (flat c))
    (hR : ∀ y, t.evR = some y →
      Configuration.enables F (projR (flat c)) y ∧ y ∉ projR (flat c)) :
    ∃ q : ParEvent E F, Configuration.enables (par E F) c q ∧ q ∉ c ∧ q.top = t := by
  have hst : IsState (insert t (flat c)) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rintro a (rfl | ha) b (rfl | hb) e he he'
      · rfl
      · exact absurd (⟨b, hb, he'⟩ : e ∈ projL (flat c)) (hL e he).2
      · exact absurd (⟨a, ha, he⟩ : e ∈ projL (flat c)) (hL e he').2
      · exact (isState_flat hc).1 a ha b hb e he he'
    · rintro a (rfl | ha) b (rfl | hb) f hf hf'
      · rfl
      · exact absurd (⟨b, hb, hf'⟩ : f ∈ projR (flat c)) (hR f hf).2
      · exact absurd (⟨a, ha, hf⟩ : f ∈ projR (flat c)) (hR f hf').2
      · exact (isState_flat hc).2.1 a ha b hb f hf hf'
    · rw [projL_insert]
      refine ⟨?_, ?_⟩
      · rintro e₁ e₂ (h1 | h1) (h2 | h2)
        · rw [h1] at h2
          exact (Option.some.inj h2) ▸ E.conflict_irrefl _
        · exact (hL e₁ h1).1.2.1 _ h2
        · exact fun hcf => (hL e₂ h2).1.2.1 _ h1 (E.conflict_symm hcf)
        · exact (isState_flat hc).2.2.1.1 h1 h2
      · rintro e e' (h | h) hle
        · rcases lt_or_eq_of_le hle with hlt | rfl
          · exact Or.inr ((hL e h).1.2.2 hlt)
          · exact Or.inl h
        · exact Or.inr ((isState_flat hc).2.2.1.2 h hle)
    · rw [projR_insert]
      refine ⟨?_, ?_⟩
      · rintro f₁ f₂ (h1 | h1) (h2 | h2)
        · rw [h1] at h2
          exact (Option.some.inj h2) ▸ F.conflict_irrefl _
        · exact (hR f₁ h1).1.2.1 _ h2
        · exact fun hcf => (hR f₂ h2).1.2.1 _ h1 (F.conflict_symm hcf)
        · exact (isState_flat hc).2.2.2.1 h1 h2
      · rintro f f' (h | h) hle
        · rcases lt_or_eq_of_le hle with hlt | rfl
          · exact Or.inr ((hR f h).1.2.2 hlt)
          · exact Or.inl h
        · exact Or.inr ((isState_flat hc).2.2.2.2 h hle)
  have htc : t ∉ flat c := by
    intro hmem
    cases htL : t.evL with
    | some x => exact (hL x htL).2 ⟨t, hmem, htL⟩
    | none =>
      cases htR : t.evR with
      | some y => exact (hR y htR).2 ⟨t, hmem, htR⟩
      | none => cases t <;> simp_all [Tag.evL, Tag.evR]
  have hS : Secured (insert t (flat c)) := Secured.step (secured_flat hfin hc) htc hst
  refine ⟨primeOf hS (Set.mem_insert _ _), ⟨hc, ?_, past_of_primeOf hc _ rfl⟩, ?_, rfl⟩
  · intro q' hq' hconf
    refine hconf (isState_of_subset hst ?_ ?_ ?_)
    · exact Set.union_subset dc_subset (fun v hv => Set.mem_insert_of_mem _ ⟨q', hq', hv⟩)
    · intro e e' he hle
      rw [projL_union] at he ⊢
      rcases he with h | h
      · exact Or.inl ((isState_dc hst _).downL h hle)
      · exact Or.inr (q'.state.downL h hle)
    · intro f f' hf hle
      rw [projR_union] at hf ⊢
      rcases hf with h | h
      · exact Or.inl ((isState_dc hst _).downR h hle)
      · exact Or.inr (q'.state.downR h hle)
  · exact fun hmem => htc ⟨_, hmem, dc_self (Set.mem_insert _ _)⟩


/-- Adding an event extends the left projection by its tag's component. -/
lemma flat_insert_projL {c : Set (ParEvent E F)} {q : ParEvent E F}
    (hp : (par E F).past q ⊆ c) {x : E.Event} (hx : q.top.evL = some x) :
    projL (flat (c ∪ {q})) = projL (flat c) ∪ {x} := by
  rw [flat_insert hp, projL_insert, Set.union_comm]
  congr 1
  ext e; rw [hx]; simp [eq_comm]

lemma flat_insert_projL_none {c : Set (ParEvent E F)} {q : ParEvent E F}
    (hp : (par E F).past q ⊆ c) (hx : q.top.evL = none) :
    projL (flat (c ∪ {q})) = projL (flat c) := by
  rw [flat_insert hp, projL_insert]
  have h : {e | q.top.evL = some e} = (∅ : Set E.Event) := by ext e; rw [hx]; simp
  rw [h, Set.empty_union]

/-- Adding an event extends the right projection by its tag's component. -/
lemma flat_insert_projR {c : Set (ParEvent E F)} {q : ParEvent E F}
    (hp : (par E F).past q ⊆ c) {y : F.Event} (hy : q.top.evR = some y) :
    projR (flat (c ∪ {q})) = projR (flat c) ∪ {y} := by
  rw [flat_insert hp, projR_insert, Set.union_comm]
  congr 1
  ext f; rw [hy]; simp [eq_comm]

lemma flat_insert_projR_none {c : Set (ParEvent E F)} {q : ParEvent E F}
    (hp : (par E F).past q ⊆ c) (hy : q.top.evR = none) :
    projR (flat (c ∪ {q})) = projR (flat c) := by
  rw [flat_insert hp, projR_insert]
  have h : {f | q.top.evR = some f} = (∅ : Set F.Event) := by ext f; rw [hy]; simp
  rw [h, Set.empty_union]

/-- Discharges a component side condition of `exists_event_tag`. -/
syntax "tag_side" (ppSpace colGt term)? : tactic
macro_rules
  | `(tactic| tag_side $h) =>
      `(tactic| intro _ hh; simp only [Tag.evL, Tag.evR] at hh; cases hh; exact $h)
  | `(tactic| tag_side) =>
      `(tactic| intro _ hh; simp [Tag.evL, Tag.evR] at hh)

/-- Component events of a tag that is enabled at `∅` are minimal. -/
lemma min_of_enables_empty {es : PES (Action Name)} {e : es.Event}
    (h : Configuration.enables es ∅ e) {e' : es.Event} (hle : e' ≤ e) : e' = e :=
  (lt_or_eq_of_le hle).elim (fun hlt => (h.2.2 hlt).elim) id


end CCS
