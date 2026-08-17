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
noncomputable def toPES (F : ConfFamily L) : PES L where
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

end Stable
