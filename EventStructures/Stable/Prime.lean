import EventStructures.Stable.Basic

/-! # Primes of a stable family

A *complete prime* is a configuration that is the history of one of its own
events, so a set with a greatest element. Ordered by inclusion, with conflict
given by incompatibility, the complete primes form a prime event structure with
the same configurations. -/

open ConfFamily

variable {L : Type*} {F : ConfFamily L}

namespace Stable

/-- Distinct events of a configuration are separated by a subconfiguration. -/
def CoincidenceFree (F : ConfFamily L) : Prop :=
  ∀ {c : Set F.Event}, F.Config c → ∀ {x y : F.Event}, x ∈ c → y ∈ c → x ≠ y →
    ∃ m, F.Config m ∧ m ⊆ c ∧ (x ∈ m ↔ y ∉ m)

/-- Every general event structure is coincidence-free: rank separates two
distinct events of a configuration. -/
lemma coincidenceFree_ges (G : GES L) : CoincidenceFree G.toFamily := by
  intro c hc x y hx hy hne
  rcases lt_or_ge (G.rank c y) (G.rank c x) with hlt | hge
  · refine ⟨{z ∈ c | G.rank c z < G.rank c y} ∪ {y}, GES.isConf_rank_lt G hc hy, ?_, ?_⟩
    · rintro z (hz | hz)
      · exact hz.1
      · exact (Set.mem_singleton_iff.mp hz) ▸ hy
    · constructor
      · rintro (hz | hz)
        · exact absurd hz.2 (by omega)
        · exact absurd (Set.mem_singleton_iff.mp hz) hne
      · intro hz
        exact absurd (Or.inr rfl) hz
  · refine ⟨{z ∈ c | G.rank c z < G.rank c x} ∪ {x}, GES.isConf_rank_lt G hc hx, ?_, ?_⟩
    · rintro z (hz | hz)
      · exact hz.1
      · exact (Set.mem_singleton_iff.mp hz) ▸ hx
    · refine ⟨fun _ => ?_, fun _ => Or.inr rfl⟩
      rintro (hz | hz)
      · exact absurd hz.2 (by omega)
      · exact hne (Set.mem_singleton_iff.mp hz).symm

/-- Histories in a general event structure are finite. -/
lemma hist_finite (G : GES L) (hF : Stable G.toFamily) {c : Set G.Event}
    (hc : G.isConf c) {x : G.Event} (hx : x ∈ c) :
    (hist G.toFamily c x).Finite := by
  induction hn : G.rank c x using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    obtain ⟨k, hk⟩ : ∃ k, G.rank c x = k + 1 := by
      have : G.rank c x ≠ 0 := by
        intro h0
        have hmem := GES.rank_mem (hc.2 x hx)
        rw [h0] at hmem
        exact hmem
      exact ⟨G.rank c x - 1, by omega⟩
    obtain ⟨-, X, hXsub, hXen⟩ := hk ▸ GES.rank_mem (hc.2 x hx)
    have hXc : ∀ g ∈ X, g ∈ c := fun g hg => GES.secApprox_subset _ (hXsub hg)
    have hXlt : ∀ g ∈ X, G.rank c g < G.rank c x :=
      fun g hg => hk ▸ Nat.lt_succ_of_le (GES.rank_le (hXsub hg))
    set U : Set G.Event := ⋃ g ∈ X, hist G.toFamily c g with hU
    have hUfin : U.Finite :=
      Set.Finite.biUnion X.finite_toSet fun g hg =>
        ih _ (hn ▸ hXlt g hg) (hXc g hg) rfl
    have hUc : U ⊆ c := by
      rintro y ⟨-, ⟨g, rfl⟩, -, ⟨hg, rfl⟩, hy⟩
      exact hist_subset hc (hXc g hg) hy
    have hXU : (X : Set G.Event) ⊆ U := fun g hg => Set.mem_biUnion hg hist_mem
    have hconf : G.isConf (U ∪ {x}) := by
      refine ⟨fun W hW => hc.1 W (hW.trans ?_), ?_⟩
      · rintro y (hy | hy)
        · exact hUc hy
        · exact (Set.mem_singleton_iff.mp hy) ▸ hx
      · have hsec : ∀ y ∈ U, ∃ m, y ∈ G.secApprox (U ∪ {x}) m := by
          rintro y ⟨-, ⟨g, rfl⟩, -, ⟨hg, rfl⟩, hy⟩
          obtain ⟨m, hm⟩ := (hist_config hF hc (hXc g hg)).2 y hy
          exact ⟨m, GES.secApprox_mono_set
            (Set.Subset.trans (fun z hz => Set.mem_biUnion hg hz) Set.subset_union_left) m hm⟩
        rintro y (hy | hy)
        · exact hsec y hy
        · obtain ⟨N, hN⟩ := GES.exists_bound (X := X) fun g hg => hsec g (hXU hg)
          exact ⟨N + 1, (Set.mem_singleton_iff.mp hy) ▸ Or.inr rfl, X, hN,
            (Set.mem_singleton_iff.mp hy) ▸ hXen⟩
    exact (hUfin.union (Set.finite_singleton x)).subset
      (hist_least hconf (by
        rintro y (hy | hy)
        · exact hUc hy
        · exact (Set.mem_singleton_iff.mp hy) ▸ hx) (Or.inr rfl))

/-- A complete prime: a configuration which is the history of one of its events. -/
def IsPrime (F : ConfFamily L) (p : Set F.Event) : Prop :=
  F.Config p ∧ ∃ x ∈ p, p = hist F p x

/-- The complete primes, ordered by inclusion. -/
def Prime (F : ConfFamily L) : Type _ := {p : Set F.Event // IsPrime F p}

instance : PartialOrder (Prime F) := Subtype.partialOrder _

namespace Prime

lemma config (p : Prime F) : F.Config p.val := p.2.1

@[simp] lemma le_iff {p q : Prime F} : p ≤ q ↔ p.val ⊆ q.val := Iff.rfl

/-- The greatest element of a complete prime. -/
noncomputable def top (p : Prime F) : F.Event := Classical.choose p.2.2

lemma top_mem (p : Prime F) : top p ∈ p.val := (Classical.choose_spec p.2.2).1

lemma eq_hist_top (p : Prime F) : p.val = hist F p.val (top p) :=
  (Classical.choose_spec p.2.2).2

/-- Any event witnessing primeness is the greatest one. -/
lemma eq_top (hcf : CoincidenceFree F) (p : Prime F) {y : F.Event}
    (hy : y ∈ p.val) (hh : p.val = hist F p.val y) : y = top p := by
  by_contra hne
  obtain ⟨m, hm, hmp, hiff⟩ := hcf p.config hy (top_mem p) hne
  by_cases hym : y ∈ m
  · exact (hiff.mp hym) (Set.Subset.antisymm hmp (hh ▸ hist_least hm hmp hym) ▸ top_mem p)
  · have htm : top p ∈ m := not_not.mp fun h => hym (hiff.mpr h)
    exact hym (Set.Subset.antisymm hmp ((eq_hist_top p) ▸ hist_least hm hmp htm) ▸ hy)

end Prime

/-- Two primes are compatible when a single configuration contains both. -/
def Compat (p q : Prime F) : Prop := ∃ c, F.Config c ∧ p.val ⊆ c ∧ q.val ⊆ c

lemma compat_self (p : Prime F) : Compat p p := ⟨p.val, p.config, subset_rfl, subset_rfl⟩

lemma Compat.symm {p q : Prime F} : Compat p q → Compat q p
  | ⟨c, hc, hp, hq⟩ => ⟨c, hc, hq, hp⟩

/-- The prime event structure of complete primes. -/
@[reducible] noncomputable def toPES (F : ConfFamily L) : PES L where
  Event := Prime F
  poEvent := Subtype.partialOrder _
  conflict p q := ¬ Compat p q
  label p := F.label (Prime.top p)
  conflict_irrefl p h := h (compat_self p)
  conflict_symm := ⟨fun _ _ h hc => h hc.symm⟩
  conflict_hereditary {_ _ _} hpq hqr hpr :=
    hpq (let ⟨c, hc, hp, hr⟩ := hpr; ⟨c, hc, hp, Set.Subset.trans hqr hr⟩)

/-- A history is its own history. -/
lemma hist_hist (hF : Stable F) {c : Set F.Event} (hc : F.Config c) {x : F.Event}
    (hx : x ∈ c) : hist F c x = hist F (hist F c x) x :=
  Set.Subset.antisymm
    (fun _ hy => Set.mem_sInter.mpr fun _ hm =>
      hist_least hm.1 (hm.2.1.trans (hist_subset hc hx)) hm.2.2 hy)
    (hist_subset (hist_config hF hc hx) hist_mem)

/-- Inside a configuration, every history is a complete prime. -/
lemma isPrime_hist (hF : Stable F) {c : Set F.Event} (hc : F.Config c) {x : F.Event}
    (hx : x ∈ c) : IsPrime F (hist F c x) :=
  ⟨hist_config hF hc hx, x, hist_mem, hist_hist hF hc hx⟩

/-- The history of `x` in `c`, as a prime. -/
noncomputable def histPrime (hF : Stable F) {c : Set F.Event} (hc : F.Config c)
    {x : F.Event} (hx : x ∈ c) : Prime F :=
  ⟨hist F c x, isPrime_hist hF hc hx⟩

/-- Complete primes have finite carriers. -/
lemma prime_val_finite (G : GES L) (hF : Stable G.toFamily) (p : Prime G.toFamily) :
    p.val.Finite :=
  (Prime.eq_hist_top p) ▸ hist_finite G hF p.config (Prime.top_mem p)

/-! ## Agreement of configurations -/

/-- The primes below a set of events. -/
def primesOf (F : ConfFamily L) (c : Set F.Event) : Set (Prime F) := {p | p.val ⊆ c}

/-- The events covered by a set of primes. -/
def flatten (F : ConfFamily L) (S : Set (Prime F)) : Set F.Event := ⋃ p ∈ S, p.val

lemma subset_flatten {S : Set (Prime F)} {p : Prime F} (hp : p ∈ S) :
    p.val ⊆ flatten F S :=
  fun _ hx => Set.mem_biUnion hp hx

/-- Configurations map to configurations. -/
lemma primesOf_isConf {c : Set F.Event} (hc : F.Config c) :
    isConf (toPES F) (primesOf F c) :=
  ⟨fun h₁ h₂ hcf => hcf ⟨c, hc, h₁, h₂⟩, fun hp hle => Set.Subset.trans hle hp⟩

/-- Every event of a configuration is the top of a prime inside it. -/
lemma mem_flatten_primesOf (hF : Stable F) {c : Set F.Event} (hc : F.Config c)
    {x : F.Event} (hx : x ∈ c) : x ∈ flatten F (primesOf F c) :=
  Set.mem_biUnion (show histPrime hF hc hx ∈ primesOf F c from hist_subset hc hx)
    (hist_mem (x := x))

/-- Flattening recovers the configuration. -/
lemma flatten_primesOf (hF : Stable F) {c : Set F.Event} (hc : F.Config c) :
    flatten F (primesOf F c) = c := by
  refine Set.Subset.antisymm ?_ fun x hx => mem_flatten_primesOf hF hc hx
  rintro x ⟨-, ⟨p, rfl⟩, -, ⟨hp, rfl⟩, hxp⟩
  exact hp hxp

/-- Inside a configuration, a prime is the history of its top. -/
lemma eq_hist_of_subset (hF : Stable F) {c : Set F.Event} (hc : F.Config c)
    {p : Prime F} (hp : p.val ⊆ c) : p.val = hist F c (Prime.top p) := by
  have htc : Prime.top p ∈ c := hp (Prime.top_mem p)
  refine Set.Subset.antisymm ?_ (hist_least p.config hp (Prime.top_mem p))
  refine (Prime.eq_hist_top p).trans_subset
    (hist_least (hist_config hF hc htc) ?_ hist_mem)
  exact hist_least p.config hp (Prime.top_mem p)

/-- Hence the prime event structure of complete primes is finitary: an event has
finitely many causal predecessors. -/
lemma toPES_finitary (G : GES L) (hF : Stable G.toFamily) :
    PES.Finitary (toPES G.toFamily) := by
  intro p
  refine Set.Finite.of_finite_image (f := Prime.top) ?_ ?_
  · refine (prime_val_finite G hF p).subset ?_
    rintro t ⟨q, hq, rfl⟩
    have hle : q.val ⊆ p.val := le_of_lt (α := (toPES G.toFamily).Event) hq
    exact hle (Prime.top_mem q)
  · rintro q hq q' hq' heq
    have hle : q.val ⊆ p.val := le_of_lt (α := (toPES G.toFamily).Event) hq
    have hle' : q'.val ⊆ p.val := le_of_lt (α := (toPES G.toFamily).Event) hq'
    have h1 : q.val = hist G.toFamily p.val (Prime.top q) :=
      eq_hist_of_subset hF p.config hle
    have h2 : q'.val = hist G.toFamily p.val (Prime.top q') :=
      eq_hist_of_subset hF p.config hle'
    exact Subtype.ext (h1.trans (heq ▸ h2.symm))

/-- A set of primes whose union is a configuration is recovered from it. -/
lemma primesOf_flatten (hF : Stable F) {S : Set (Prime F)}
    (hS : isConf (toPES F) S) (hflat : F.Config (flatten F S)) :
    primesOf F (flatten F S) = S := by
  refine Set.Subset.antisymm (fun p hp => ?_) (fun p hp => subset_flatten hp)
  obtain ⟨-, ⟨q, rfl⟩, -, ⟨hq, rfl⟩, htq⟩ := hp (Prime.top_mem p)
  refine hS.2 hq (show p.val ⊆ q.val from ?_)
  rw [eq_hist_of_subset hF hflat hp]
  exact hist_least q.config (subset_flatten hq) htq

/-- The label of a history-prime is the label of the event it is the history of. -/
lemma label_histPrime (hF : Stable F) (hcf : CoincidenceFree F) {c : Set F.Event}
    (hc : F.Config c) {x : F.Event} (hx : x ∈ c) :
    (toPES F).label (histPrime hF hc hx) = F.label x := by
  exact congrArg F.label
    (Prime.eq_top hcf (histPrime hF hc hx) hist_mem (hist_hist hF hc hx)).symm

/-! ## Firing one prime

Adding an enabled prime to a configuration adds exactly one event, its top. -/

/-- A non-top event of a prime is the top of a strictly smaller prime. -/
lemma histPrime_lt (hF : Stable F) (hcf : CoincidenceFree F) (p : Prime F)
    {t : F.Event} (ht : t ∈ p.val) (hne : t ≠ Prime.top p) :
    histPrime hF p.config ht < p := by
  refine lt_of_le_of_ne (hist_subset p.config ht) fun heq => ?_
  exact hne (Prime.eq_top hcf p ht (congrArg Subtype.val heq).symm)

/-- Every event of an enabled prime other than its top is already present. -/
lemma val_subset_flatten (hF : Stable F) (hcf : CoincidenceFree F)
    {c : Set (Prime F)} {p : Prime F} (hpast : ∀ q : Prime F, q < p → q ∈ c) :
    p.val ⊆ flatten F c ∪ {Prime.top p} := by
  intro t ht
  by_cases hne : t = Prime.top p
  · exact Or.inr hne
  · exact Or.inl (subset_flatten (hpast _ (histPrime_lt hF hcf p ht hne)) hist_mem)

/-- Firing a prime adds exactly its top. -/
lemma flatten_insert (hF : Stable F) (hcf : CoincidenceFree F)
    {c : Set (Prime F)} {p : Prime F} (hpast : ∀ q : Prime F, q < p → q ∈ c) :
    flatten F (c ∪ {p}) = flatten F c ∪ {Prime.top p} := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro x ⟨-, ⟨q, rfl⟩, -, ⟨hq | hq, rfl⟩, hxq⟩
    · exact Or.inl (subset_flatten hq hxq)
    · exact val_subset_flatten hF hcf hpast ((Set.mem_singleton_iff.mp hq) ▸ hxq)
  · rintro x (hx | hx)
    · obtain ⟨-, ⟨q, rfl⟩, -, ⟨hq, rfl⟩, hxq⟩ := hx
      exact subset_flatten (Or.inl hq) hxq
    · exact subset_flatten (Or.inr rfl) ((Set.mem_singleton_iff.mp hx) ▸ Prime.top_mem p)

end Stable
