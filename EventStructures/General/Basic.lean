import EventStructures.Family.Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.Preorder.Finite
import Mathlib.Order.Minimal

/-! # General event structures

Consistency is n-ary and causality is disjunctive.
-/

/-- Events, an n-ary consistency predicate, and an enabling relation. -/
structure GES (Label : Type*) where
  Event : Type*
  Con : Finset Event → Prop
  enable : Finset Event → Event → Prop
  label : Event → Label
  con_empty : Con ∅
  con_subset : ∀ {X Y : Finset Event}, Con Y → X ⊆ Y → Con X
  enable_mono : ∀ {X Y : Finset Event} {e}, enable X e → X ⊆ Y → Con Y → enable Y e

namespace GES

variable {L : Type*} (G : GES L)

/-- Notation for the enabling relation. -/
local infix:50 " ⊢ " => G.enable

/-- Events of `x` secured in at most `n` steps. -/
def secApprox (x : Set G.Event) : ℕ → Set G.Event
  | 0 => ∅
  | n + 1 => {e ∈ x | ∃ X : Finset G.Event, ↑X ⊆ secApprox x n ∧ X ⊢ e}

variable {G}

lemma secApprox_subset {x : Set G.Event} : ∀ n, G.secApprox x n ⊆ x
  | 0 => fun _ h => h.elim
  | _ + 1 => fun _ h => h.1

lemma secApprox_succ {x : Set G.Event} : ∀ n, G.secApprox x n ⊆ G.secApprox x (n + 1)
  | 0 => fun _ h => h.elim
  | n + 1 => fun _ h => ⟨h.1, h.2.imp fun _ hX => ⟨hX.1.trans (secApprox_succ n), hX.2⟩⟩

lemma secApprox_mono {x : Set G.Event} {m n : ℕ} (h : m ≤ n) :
    G.secApprox x m ⊆ G.secApprox x n := by
  induction h with
  | refl => exact subset_rfl
  | step _ ih => exact ih.trans (secApprox_succ _)

/-- Securedness only ever grows with the ambient set. -/
lemma secApprox_mono_set {x y : Set G.Event} (hxy : x ⊆ y) :
    ∀ n, G.secApprox x n ⊆ G.secApprox y n
  | 0 => fun _ h => h.elim
  | n + 1 => fun _ h => ⟨hxy h.1, h.2.imp fun _ hX => ⟨hX.1.trans (secApprox_mono_set hxy n), hX.2⟩⟩

variable (G)

/-- Every finite subset is consistent. -/
def Consistent (s : Set G.Event) : Prop := ∀ X : Finset G.Event, ↑X ⊆ s → G.Con X

/-- Consistent, and every event secured inside it. -/
def isConf (x : Set G.Event) : Prop :=
  G.Consistent x ∧ ∀ e ∈ x, ∃ n, e ∈ G.secApprox x n

/-- The least number of steps securing `e` in `x`. -/
noncomputable def rank (x : Set G.Event) (e : G.Event) : ℕ :=
  sInf {n | e ∈ G.secApprox x n}

variable {G}

lemma rank_mem {x : Set G.Event} {e : G.Event} (h : ∃ n, e ∈ G.secApprox x n) :
    e ∈ G.secApprox x (G.rank x e) :=
  Nat.sInf_mem h

lemma rank_le {x : Set G.Event} {e : G.Event} {n : ℕ} (h : e ∈ G.secApprox x n) :
    G.rank x e ≤ n :=
  Nat.sInf_le h

/-- A finite set of secured events is secured uniformly. -/
lemma exists_bound {x : Set G.Event} {X : Finset G.Event}
    (h : ∀ g ∈ X, ∃ n, g ∈ G.secApprox x n) : ∃ N, ↑X ⊆ G.secApprox x N := by
  classical
  induction X using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert g X _ ih =>
    obtain ⟨n, hn⟩ := h g (Finset.mem_insert_self g X)
    obtain ⟨N, hN⟩ := ih fun f hf => h f (Finset.mem_insert_of_mem hf)
    refine ⟨max n N, ?_⟩
    rw [Finset.coe_insert]
    exact Set.insert_subset (secApprox_mono (le_max_left n N) hn)
      (hN.trans (secApprox_mono (le_max_right n N)))

/-- Every event of a configuration has an enabling set inside it. -/
lemma exists_enabling {x : Set G.Event} (hx : G.isConf x) {e : G.Event} (he : e ∈ x) :
    ∃ Y : Finset G.Event, (Y ⊢ e) ∧ ↑Y ⊆ x := by
  obtain ⟨n, hn⟩ := hx.2 e he
  cases n with
  | zero => exact hn.elim
  | succ k =>
    obtain ⟨-, Y, hYsub, hYen⟩ := hn
    exact ⟨Y, hYen, hYsub.trans (secApprox_subset k)⟩

variable (G)

/-- The empty set is a configuration. -/
lemma isConf_empty : G.isConf ∅ :=
  ⟨fun _ hX => Finset.coe_eq_empty.mp (Set.subset_empty_iff.mp hX) ▸ G.con_empty,
   fun _ h => h.elim⟩

/-- An event of the gap of greatest rank can be removed. -/
lemma isConf_secured {x y : Set G.Event} (hx : G.isConf x) (hy : G.isConf y)
    (hsub : y ⊆ x) (hfin : (x \ y).Finite) (hne : x ≠ y) :
    ∃ e ∈ x \ y, G.isConf (x \ {e}) := by
  classical
  have hDne : (x \ y).Nonempty := by
    by_contra h
    exact hne (Set.Subset.antisymm (fun z hz => by
      by_contra hzy; exact h ⟨z, hz, hzy⟩) hsub)
  obtain ⟨e, hmax⟩ := hfin.exists_maximalFor (G.rank x) _ hDne
  have heD : e ∈ x \ y := hmax.1
  have hemax : ∀ f ∈ x \ y, G.rank x f ≤ G.rank x e := fun _ hf => not_lt.mp (hmax.not_gt hf)
  -- induction: every `f ∈ x` other than `e` is secured without `e`
  have key : ∀ n f, f ∈ x → f ≠ e → G.rank x f = n → ∃ m, f ∈ G.secApprox (x \ {e}) m := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rintro f hf hfe rfl
      by_cases hfy : f ∈ y
      · obtain ⟨m, hm⟩ := hy.2 f hfy
        have hyx : y ⊆ x \ {e} := fun z hz =>
          ⟨hsub hz, fun hze => heD.2 (Set.mem_singleton_iff.mp hze ▸ hz)⟩
        exact ⟨m, secApprox_mono_set hyx m hm⟩
      · obtain ⟨k, hk⟩ : ∃ k, G.rank x f = k + 1 := by
          have hpos : G.rank x f ≠ 0 := by
            intro h0
            have hmem := rank_mem (hx.2 f hf)
            rw [h0] at hmem
            exact hmem
          exact ⟨G.rank x f - 1, by omega⟩
        obtain ⟨-, X, hXsub, hXen⟩ := hk ▸ rank_mem (hx.2 f hf)
        have hXlt : ∀ g ∈ X, G.rank x g < G.rank x f :=
          fun g hg => hk ▸ Nat.lt_succ_of_le (rank_le (hXsub hg))
        obtain ⟨N, hN⟩ := exists_bound (x := x \ {e}) fun g hg => by
          have hgx : g ∈ x := secApprox_subset _ (hXsub hg)
          have hge : g ≠ e := by
            rintro rfl
            have h₁ := hXlt g hg
            have h₂ := hemax f ⟨hf, hfy⟩
            omega
          exact ih _ (hXlt g hg) g hgx hge rfl
        exact ⟨N + 1, ⟨hf, fun hfe' => hfe (Set.mem_singleton_iff.mp hfe')⟩, X, hN, hXen⟩
  exact ⟨e, heD, fun X hX => hx.1 X (hX.trans Set.sdiff_subset),
    fun f hf => key _ f hf.1 (fun h => hf.2 (Set.mem_singleton_iff.mpr h)) rfl⟩

/-- The events of `c` of rank strictly below that of `x`, together with `x`,
form a configuration. -/
lemma isConf_rank_lt {c : Set G.Event} (hc : G.isConf c) {x : G.Event} (hx : x ∈ c) :
    G.isConf ({z ∈ c | G.rank c z < G.rank c x} ∪ {x}) := by
  set m : Set G.Event := {z ∈ c | G.rank c z < G.rank c x} ∪ {x} with hm
  have hmc : m ⊆ c := by
    rintro z (hz | hz)
    · exact hz.1
    · exact (Set.mem_singleton_iff.mp hz) ▸ hx
  have hlt : ∀ {z}, z ∈ m → ∀ {g}, G.rank c g < G.rank c z → g ∈ c → g ∈ m := by
    rintro z (hz | hz) g hg hgc
    · exact Or.inl ⟨hgc, hg.trans hz.2⟩
    · exact Or.inl ⟨hgc, (Set.mem_singleton_iff.mp hz) ▸ hg⟩
  refine ⟨fun X hX => hc.1 X (hX.trans hmc), ?_⟩
  have key : ∀ n z, z ∈ m → G.rank c z = n → ∃ k, z ∈ G.secApprox m k := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rintro z hz rfl
      obtain ⟨k, hk⟩ : ∃ k, G.rank c z = k + 1 := by
        have : G.rank c z ≠ 0 := by
          intro h0
          have hmem := rank_mem (hc.2 z (hmc hz))
          rw [h0] at hmem
          exact hmem
        exact ⟨G.rank c z - 1, by omega⟩
      obtain ⟨-, X, hXsub, hXen⟩ := hk ▸ rank_mem (hc.2 z (hmc hz))
      obtain ⟨N, hN⟩ := exists_bound (x := m) (X := X) fun g hg => by
        have hgc : g ∈ c := secApprox_subset _ (hXsub hg)
        have hglt : G.rank c g < G.rank c z := hk ▸ Nat.lt_succ_of_le (rank_le (hXsub hg))
        exact ih _ hglt g (hlt hz hglt hgc) rfl
      exact ⟨N + 1, hz, X, hN, hXen⟩
  exact fun z hz => key _ z hz rfl

/-- The image of a set under a partial map on events. -/
def pmapSet {L' : Type*} {G : GES L} {H : GES L'} (φ : G.Event → Option H.Event)
    (c : Set G.Event) : Set H.Event :=
  {x | ∃ u ∈ c, φ u = some x}

lemma subset_pmapSet {L' : Type*} {G : GES L} {H : GES L'}
    {φ : G.Event → Option H.Event} {c : Set G.Event}
    {u : G.Event} {x : H.Event} (hu : u ∈ c) (hx : φ u = some x) : x ∈ pmapSet φ c :=
  ⟨u, hu, hx⟩

lemma pmapSet_mono {L' : Type*} {G : GES L} {H : GES L'}
    {φ : G.Event → Option H.Event} {c d : Set G.Event}
    (h : c ⊆ d) : pmapSet φ c ⊆ pmapSet φ d :=
  fun _ ⟨u, hu, hx⟩ => ⟨u, h hu, hx⟩

/-- Configurations transfer along a partial map that carries enabling sets to
enabling sets. -/
lemma isConf_pmap {L' : Type*} {G : GES L} {H : GES L'}
    (φ : G.Event → Option H.Event)
    (hcon : ∀ {c : Set G.Event}, G.Consistent c → H.Consistent (pmapSet φ c))
    (hen : ∀ {X : Finset G.Event} {u : G.Event} {x : H.Event},
      G.enable X u → φ u = some x →
      ∃ Y : Finset H.Event, (∀ y ∈ Y, y ∈ pmapSet φ (X : Set G.Event)) ∧ H.enable Y x)
    {c : Set G.Event} (hc : G.isConf c) : H.isConf (pmapSet φ c) := by
  refine ⟨hcon hc.1, ?_⟩
  have key : ∀ n u, u ∈ c → G.rank c u = n →
      ∀ x, φ u = some x → ∃ m, x ∈ H.secApprox (pmapSet φ c) m := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rintro u hu rfl x hx
      obtain ⟨k, hk⟩ : ∃ k, G.rank c u = k + 1 := by
        have : G.rank c u ≠ 0 := by
          intro h0
          have hmem := rank_mem (hc.2 u hu)
          rw [h0] at hmem
          exact hmem
        exact ⟨G.rank c u - 1, by omega⟩
      obtain ⟨-, X, hXsub, hXen⟩ := hk ▸ rank_mem (hc.2 u hu)
      obtain ⟨Y, hY, hYen⟩ := hen hXen hx
      obtain ⟨N, hN⟩ := exists_bound (x := pmapSet φ c) (X := Y) fun y hy => by
        obtain ⟨v, hv, hev⟩ := hY y hy
        have hvc : v ∈ c := secApprox_subset _ (hXsub hv)
        refine ih _ ?_ v hvc rfl y hev
        exact hk ▸ Nat.lt_succ_of_le (rank_le (hXsub hv))
      exact ⟨N + 1, ⟨u, hu, hx⟩, Y, hN, hYen⟩
  rintro x ⟨u, hu, hx⟩
  exact key _ u hu rfl x hx

/-- Conversely, an event whose image is enabled extends a configuration, provided
enabling sets pull back. -/
lemma isConf_insert_pmap {L' : Type*} {G : GES L} {H : GES L'}
    (φ : G.Event → Option H.Event)
    {c : Set G.Event} {u : G.Event} {x : H.Event} (hc : G.isConf c) (hφ : φ u = some x)
    (hcon : G.Consistent (c ∪ {u}))
    (hback : ∀ Y : Finset H.Event, (∀ y ∈ Y, y ∈ pmapSet φ c) → H.enable Y x →
      ∃ X : Finset G.Event, (X : Set G.Event) ⊆ c ∧ G.enable X u)
    (hx : H.isConf (pmapSet φ c ∪ {x})) : G.isConf (c ∪ {u}) := by
  refine ⟨hcon, ?_⟩
  have hmono : ∀ {v : G.Event}, v ∈ c → ∃ n, v ∈ G.secApprox (c ∪ {u}) n := by
    intro v hv
    obtain ⟨n, hn⟩ := hc.2 v hv
    exact ⟨n, secApprox_mono_set Set.subset_union_left n hn⟩
  rintro v (hv | hv)
  · exact hmono hv
  · replace hv : v = u := hv
    subst hv
    -- the enabling set of `x` avoids `x`, so it lies in the image of `c`
    obtain ⟨k, hk⟩ : ∃ k, H.rank (pmapSet φ c ∪ {x}) x = k + 1 := by
      have : H.rank (pmapSet φ c ∪ {x}) x ≠ 0 := by
        intro h0
        have hmem := rank_mem (hx.2 x (Or.inr rfl))
        rw [h0] at hmem
        exact hmem
      exact ⟨H.rank (pmapSet φ c ∪ {x}) x - 1, by omega⟩
    obtain ⟨-, Y, hYsub, hYen⟩ := hk ▸ rank_mem (hx.2 x (Or.inr rfl))
    have hYc : ∀ y ∈ Y, y ∈ pmapSet φ c := by
      intro y hy
      rcases secApprox_subset _ (hYsub hy) with h | h
      · exact h
      · exact absurd (hk ▸ Nat.lt_succ_of_le (rank_le (hYsub hy)) :
          H.rank (pmapSet φ c ∪ {x}) y < H.rank (pmapSet φ c ∪ {x}) x)
          (by rw [Set.mem_singleton_iff.mp h]; omega)
    obtain ⟨X, hXc, hXen⟩ := hback Y hYc hYen
    obtain ⟨N, hN⟩ := exists_bound (X := X) fun g hg => hmono (hXc (by exact_mod_cast hg))
    exact ⟨N + 1, Or.inr rfl, X, hN, hXen⟩

/-- The configuration family of a general event structure. -/
def toFamily : ConfFamily L where
  Event := G.Event
  Config := G.isConf
  label := G.label
  empty_mem := G.isConf_empty
  secured := G.isConf_secured

@[simp] lemma toFamily_Event : G.toFamily.Event = G.Event := rfl
@[simp] lemma toFamily_Config : G.toFamily.Config = G.isConf := rfl

end GES
