import OAI.SetTheory.PartitionPrinciple.Forcing.ConditionQuantifiers

namespace OAI


namespace PartitionPilot.Forcing

section
universe u v
variable {Upper : Type u} {Lower : Type v} [PartialOrder Upper] [PartialOrder Lower]

structure CompleteProjection (restriction : Upper →o Lower)
    (inclusion : Lower ↪o Upper) : Prop where
  retract : ∀ q, restriction (inclusion q) = q
  le_include_iff : ∀ p q, p ≤ inclusion q ↔ restriction p ≤ q
  lift : ∀ p q, q ≤ restriction p → ∃ r, r ≤ p ∧ restriction r = q

namespace CompleteProjection
variable {restriction : Upper →o Lower} {inclusion : Lower ↪o Upper}
variable (projection : CompleteProjection restriction inclusion)
include projection

theorem le_include_restriction (p : Upper) : p ≤ inclusion (restriction p) :=
  (projection.le_include_iff p (restriction p)).2 le_rfl

theorem compatible_include_iff (p : Upper) (q : Lower) :
    Compatible p (inclusion q) ↔ Compatible (restriction p) q := by
  constructor
  · rintro ⟨r, rp, rq⟩
    exact ⟨restriction r, restriction.monotone rp, (projection.le_include_iff r q).1 rq⟩
  · rintro ⟨q', below, included⟩
    obtain ⟨r, rp, equal⟩ := projection.lift p q' below
    refine ⟨r, rp, (projection.le_include_iff r q).2 ?_⟩
    exact equal.symm ▸ included

theorem included_compatible_iff (p q : Lower) :
    Compatible (inclusion p) (inclusion q) ↔ Compatible p q := by
  rw [projection.compatible_include_iff, projection.retract]

theorem dense_preimage {E : Set Lower} (dense : Dense E) :
    Dense {p : Upper | restriction p ∈ E} := by
  intro p
  obtain ⟨q, below, member⟩ := dense (restriction p)
  obtain ⟨r, rp, equal⟩ := projection.lift p q below
  refine ⟨r, rp, ?_⟩
  change restriction r ∈ E
  rw [equal]
  exact member

theorem predense_inclusion {E : Set Lower}
    (predense : ∀ q : Lower, ∃ r ∈ E, Compatible q r) :
    ∀ p : Upper, ∃ r ∈ E, Compatible p (inclusion r) := by
  intro p
  obtain ⟨r, member, compatible⟩ := predense (restriction p)
  exact ⟨r, member, (projection.compatible_include_iff p r).2 compatible⟩

def projectedFilter (H : ConditionFilter Upper) : ConditionFilter Lower where
  mem q := H.mem (inclusion q)
  nonempty := by
    obtain ⟨p, member⟩ := H.nonempty
    exact ⟨restriction p, H.upward member (projection.le_include_restriction p)⟩
  upward := by
    intro p q member below
    exact H.upward member (inclusion.monotone below)
  directed := by
    intro p q hp hq
    obtain ⟨r, member, rp, rq⟩ := H.directed hp hq
    exact ⟨restriction r, H.upward member (projection.le_include_restriction r),
      (projection.le_include_iff r p).1 rp, (projection.le_include_iff r q).1 rq⟩

theorem projectedFilter_mem_iff (H : ConditionFilter Upper) (q : Lower) :
    (projection.projectedFilter H).mem q ↔
      ∃ p : Upper, H.mem p ∧ restriction p = q := by
  constructor
  · intro member
    exact ⟨inclusion q, member, projection.retract q⟩
  · rintro ⟨p, member, rfl⟩
    exact H.upward member (projection.le_include_restriction p)

theorem projectedFilter_meets_iff (H : ConditionFilter Upper) (E : Set Lower) :
    (projection.projectedFilter H).Meets E ↔ H.Meets {p : Upper | restriction p ∈ E} := by
  constructor
  · rintro ⟨q, member, hq⟩
    obtain ⟨p, hp, rfl⟩ := (projection.projectedFilter_mem_iff H q).1 member
    exact ⟨p, hp, hq⟩
  · rintro ⟨p, member, hp⟩
    exact ⟨restriction p, (projection.projectedFilter_mem_iff H (restriction p)).2
      ⟨p, member, rfl⟩, hp⟩

theorem projectedFilter_generic (H : ConditionFilter Upper) (family : Set (Set Lower))
    (generic : H.GenericFor ((fun E : Set Lower => {p : Upper | restriction p ∈ E}) '' family)) :
    (projection.projectedFilter H).GenericFor family := by
  intro E member dense
  exact (projection.projectedFilter_meets_iff H E).2
    (generic _ ⟨E, member, rfl⟩ (projection.dense_preimage dense))

end CompleteProjection
end



namespace CompleteProjection
universe u v
variable {Upper : Type u} {Lower : Type v} [PartialOrder Upper] [PartialOrder Lower]
variable {restriction : Upper →o Lower} {inclusion : Lower ↪o Upper}
variable (projection : CompleteProjection restriction inclusion)
include projection

theorem denseBelow_preimage_iff (q : Upper) (E : Set Lower) :
    DenseBelow q {r | restriction r ∈ E} ↔ DenseBelow (restriction q) E := by
  constructor
  · intro dense p pq
    obtain ⟨r, rq, rp⟩ := projection.lift q p pq
    obtain ⟨v, vr, member⟩ := dense r rq
    exact ⟨restriction v, (restriction.monotone vr).trans_eq rp, member⟩
  · intro dense r rq
    obtain ⟨p, pr, member⟩ := dense (restriction r) (restriction.monotone rq)
    obtain ⟨v, vr, vp⟩ := projection.lift r p pr
    exact ⟨v, vr, show restriction v ∈ E from vp.symm ▸ member⟩

end CompleteProjection



namespace Name
open SetRealization
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]
variable (s : Presentation P) (t : Presentation Q)
variable (pi : Q →o P) (inc : P ↪o Q) (projection : CompleteProjection pi inc)
include projection

theorem forcesEq_rename_completeProjection (q : Q) (σ τ : Name s) :
    ForcesEq q (rename t inc σ) (rename t inc τ) ↔ ForcesEq (pi q) σ τ := by
  induction σ using inductionOn generalizing τ q with
  | step σ ih =>
    rw [ForcesEq, ForcesEq]
    constructor
    · rintro ⟨left, right⟩
      constructor
      · intro ρ r hr p pq pr
        obtain ⟨v, vq, vp⟩ := projection.lift q p pq
        have vr : v ≤ inc r := (projection.le_include_iff v r).2 (vp.symm ▸ pr)
        have entry := (entry_rename t inc σ (rename t inc ρ) (inc r)).2 ⟨ρ, r, hr, rfl, rfl⟩
        obtain ⟨w, wv, ν, k, hk, wk, eq⟩ := left _ _ entry v vq vr
        obtain ⟨ν₀, k₀, old, rfl, rfl⟩ := (entry_rename t inc τ ν k).1 hk
        exact ⟨pi w, (pi.monotone wv).trans_eq vp, ν₀, k₀, old,
          (projection.le_include_iff w k₀).1 wk, (ih ρ r hr (q := w) (τ := ν₀)).1 eq⟩
      · intro ν k hk p pq pk
        obtain ⟨v, vq, vp⟩ := projection.lift q p pq
        have vk : v ≤ inc k := (projection.le_include_iff v k).2 (vp.symm ▸ pk)
        have entry := (entry_rename t inc τ (rename t inc ν) (inc k)).2 ⟨ν, k, hk, rfl, rfl⟩
        obtain ⟨w, wv, ρ, r, hr, wr, eq⟩ := right _ _ entry v vq vk
        obtain ⟨ρ₀, r₀, old, rfl, rfl⟩ := (entry_rename t inc σ ρ r).1 hr
        exact ⟨pi w, (pi.monotone wv).trans_eq vp, ρ₀, r₀, old,
          (projection.le_include_iff w r₀).1 wr, (ih ρ₀ r₀ old (q := w) (τ := ν)).1 eq⟩
    · rintro ⟨left, right⟩
      constructor
      · intro ρ r hr v vq vr
        obtain ⟨ρ₀, r₀, old, rfl, rfl⟩ := (entry_rename t inc σ ρ r).1 hr
        obtain ⟨p, pv, ν, k, hk, pk, eq⟩ :=
          left ρ₀ r₀ old (pi v) (pi.monotone vq) ((projection.le_include_iff v r₀).1 vr)
        obtain ⟨w, wv, wp⟩ := projection.lift v p pv
        refine ⟨w, wv, rename t inc ν, inc k,
          (entry_rename t inc τ (rename t inc ν) (inc k)).2 ⟨ν, k, hk, rfl, rfl⟩,
          (projection.le_include_iff w k).2 (wp.symm ▸ pk), ?_⟩
        exact (ih ρ₀ r₀ old (q := w) (τ := ν)).2 (wp.symm ▸ eq)
      · intro ν k hk v vq vk
        obtain ⟨ν₀, k₀, old, rfl, rfl⟩ := (entry_rename t inc τ ν k).1 hk
        obtain ⟨p, pv, ρ, r, hr, pr, eq⟩ :=
          right ν₀ k₀ old (pi v) (pi.monotone vq) ((projection.le_include_iff v k₀).1 vk)
        obtain ⟨w, wv, wp⟩ := projection.lift v p pv
        refine ⟨w, wv, rename t inc ρ, inc r,
          (entry_rename t inc σ (rename t inc ρ) (inc r)).2 ⟨ρ, r, hr, rfl, rfl⟩,
          (projection.le_include_iff w r).2 (wp.symm ▸ pr), ?_⟩
        exact (ih ρ r hr (q := w) (τ := ν₀)).2 (wp.symm ▸ eq)

end Name



namespace Name
open SetRealization
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]
variable (s : Presentation P) (t : Presentation Q)
variable (pi : Q →o P) (inc : P ↪o Q) (projection : CompleteProjection pi inc)
include projection

theorem memWitness_rename_completeProjection (q : Q) (σ τ : Name s) :
    q ∈ MemWitness (rename t inc σ) (rename t inc τ) ↔ pi q ∈ MemWitness σ τ := by
  constructor
  · rintro ⟨ν, r, entry, qr, eq⟩
    obtain ⟨ν₀, r₀, old, rfl, rfl⟩ := (entry_rename t inc τ ν r).1 entry
    exact ⟨ν₀, r₀, old, (projection.le_include_iff q r₀).1 qr,
      (forcesEq_rename_completeProjection s t pi inc projection q σ ν₀).1 eq⟩
  · rintro ⟨ν, r, entry, qr, eq⟩
    exact ⟨rename t inc ν, inc r,
      (entry_rename t inc τ (rename t inc ν) (inc r)).2 ⟨ν, r, entry, rfl, rfl⟩,
      (projection.le_include_iff q r).2 qr,
      (forcesEq_rename_completeProjection s t pi inc projection q σ ν).2 eq⟩

theorem forcesMem_rename_completeProjection (q : Q) (σ τ : Name s) :
    ForcesMem q (rename t inc σ) (rename t inc τ) ↔ ForcesMem (pi q) σ τ := by
  have witnesses : MemWitness (rename t inc σ) (rename t inc τ) =
      {r : Q | pi r ∈ MemWitness σ τ} := by
    apply Set.ext
    intro r
    exact memWitness_rename_completeProjection s t pi inc projection r σ τ
  change DenseBelow q _ ↔ DenseBelow (pi q) _
  rw [witnesses]
  exact projection.denseBelow_preimage_iff q (MemWitness σ τ)

end Name



namespace CompleteProjection
open SetRealization
universe u
variable {Upper Lower : Type u} [PartialOrder Upper] [PartialOrder Lower]
variable {restriction : Upper →o Lower} {inclusion : Lower ↪o Upper}
variable (projection : CompleteProjection restriction inclusion)
include projection

theorem predense_inclusion_iff {E : Set Lower} :
    (∀ p : Upper, ∃ r ∈ E, Compatible p (inclusion r)) ↔
      (∀ q : Lower, ∃ r ∈ E, Compatible q r) := by
  constructor
  · intro predense q
    obtain ⟨r, member, common⟩ := predense (inclusion q)
    exact ⟨r, member, (projection.included_compatible_iff q r).1 common⟩
  · exact projection.predense_inclusion

theorem raw_predense_restriction (s : Presentation Upper) (t : Presentation Lower)
    (unchanged : ∀ q, s.encode (inclusion q) = t.encode q)
    {A : ZFSet.{u}} (within : A ⊆ t.carrier)
    (predense : ∀ q ∈ s.carrier, ∃ p ∈ A, ∃ r ∈ s.carrier,
      ZFSet.pair r q ∈ s.conditionOrder ∧ ZFSet.pair r p ∈ s.conditionOrder) :
    ∀ q ∈ t.carrier, ∃ p ∈ A, ∃ r ∈ t.carrier,
      ZFSet.pair r q ∈ t.conditionOrder ∧ ZFSet.pair r p ∈ t.conditionOrder := by
  have upper : ∀ p : Upper, ∃ q, t.encode q ∈ A ∧ Compatible p (inclusion q) := by
    intro p
    obtain ⟨x, hx, z, hz, zp, zx⟩ := predense (s.encode p) (s.encode_mem p)
    obtain ⟨q, qCode⟩ := (t.mem_carrier x).1 (within hx)
    obtain ⟨r, rCode⟩ := (s.mem_carrier z).1 hz
    refine ⟨q, qCode.symm ▸ hx, r, ?_, ?_⟩
    · apply (s.pair_mem_conditionOrder r p).1
      rwa [rCode]
    · apply (s.pair_mem_conditionOrder r (inclusion q)).1
      rwa [rCode, unchanged q, qCode]
  have lower := (projection.predense_inclusion_iff (E := {q | t.encode q ∈ A})).1 upper
  intro x hx
  obtain ⟨q, qCode⟩ := (t.mem_carrier x).1 hx
  obtain ⟨p, hp, r, rq, rp⟩ := lower q
  refine ⟨t.encode p, hp, t.encode r, t.encode_mem r, ?_,
    (t.pair_mem_conditionOrder r p).2 rp⟩
  rw [← qCode]
  exact (t.pair_mem_conditionOrder r q).2 rq

end CompleteProjection

end PartitionPilot.Forcing

end OAI
