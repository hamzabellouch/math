import OAI.SetTheory.PartitionPrinciple.Forcing.GroundFilterCopies

namespace OAI

namespace PartitionPilot.Forcing

namespace TransitiveGround

universe u
variable (M N : TransitiveGround.{u})

theorem groundEmbeddable_of_inclusion (includes : M.sets ⊆ N.sets)
    {A B : ZFSet.{u}} (small : M.groundEmbeddable A B) : N.groundEmbeddable A B := by
  obtain ⟨f, hf, injection⟩ := small
  exact ⟨f, includes hf, injection⟩

end TransitiveGround

section

universe u

inductive CodedGrowthLayer (M : TransitiveGround.{u})
    (Space sourceOrder sourceMeet : ZFSet.{u} → ZFSet.{u})
    (L r μ birth t : ZFSet.{u}) : Type (u + 1) where
  | countablePoints (D : ZFSet.{u}) (ground : D ∈ M.sets)
      (small : M.groundEmbeddable D ZFSet.omega)
      (cover : ∀ x ∈ L, ZFSet.pair x t ∈ birth → x ∈ D)
  | copies (I parts : ZFSet.{u}) (groundI : I ∈ M.sets)
      (small : M.groundEmbeddable I ZFSet.omega) (groundParts : parts ∈ M.sets)
      (index e : ZFSet.{u} → ZFSet.{u}) (earlier : ∀ i ∈ I, index i ∈ t)
      (groundCopy : ∀ i ∈ I, e i ∈ M.sets)
      (embedding : ∀ i ∈ I, MeetEmbeddingCode (Space (index i)) L
        (sourceOrder (index i)) r (sourceMeet (index i)) μ (e i))
      (cover : ∀ x ∈ L, ZFSet.pair x t ∈ birth → ∃ i ∈ I, ZFSet.pair i x ∈ parts)
      (inCopy : ∀ i ∈ I, ∀ x ∈ L, ZFSet.pair i x ∈ parts →
        x ∈ relationImage (Space (index i)) L (e i))
  | separated (I : Type u) (index e : I → ZFSet.{u}) (earlier : ∀ i, index i ∈ t)
      (groundCopy : ∀ i, e i ∈ M.sets)
      (embedding : ∀ i, MeetEmbeddingCode (Space (index i)) L
        (sourceOrder (index i)) r (sourceMeet (index i)) μ (e i))
      (component : {x : ZFSet.{u} // x ∈ L ∧ ZFSet.pair x t ∈ birth} → I)
      (cover : ∀ x : {x : ZFSet.{u} // x ∈ L ∧ ZFSet.pair x t ∈ birth},
        x.val ∈ relationImage (Space (index (component x))) L (e (component x)))
      (separation : ∀ x y : {x : ZFSet.{u} // x ∈ L ∧ ZFSet.pair x t ∈ birth},
        component x ≠ component y → OldBridgeCode L r μ birth t x.val y.val)

namespace CodedGrowthLayer

open SetFormula

theorem internal_countable_essentials
    {M : TransitiveGround.{u}} {Space sourceOrder sourceMeet : ZFSet.{u} → ZFSet.{u}}
    {L F T r μ birth t : ZFSet.{u}}
    (layer : CodedGrowthLayer M Space sourceOrder sourceMeet L r μ birth t)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hL : L ∈ M.sets) (hr : r ∈ M.sets) (hBirth : birth ∈ M.sets)
    (hF : F ∈ M.sets) (hT : T ∈ M.sets) (ht : t ∈ M.sets)
    (meet : MeetOrderCode L r μ) (filter : MeetFilterCode L r μ F)
    (born : ZFSet.IsFunc L T birth)
    (earlier : ∀ s ∈ t, Space s ∈ M.sets ∧
      MeetOrderCode (Space s) (sourceOrder s) (sourceMeet s) ∧
      ∀ P ∈ M.sets, MeetFilterCode (Space s) (sourceOrder s) (sourceMeet s) P →
        M.InternalCountableBelow (sourceOrder s) P P) :
    M.InternalCountableBelow r F (essentialBirthFiber F T r birth t) := by
  classical
  have groundFiber := M.essentialBirthFiber_mem separation hF hT hr hBirth ht
  have positive : essentialBirthFiber F T r birth t ⊆ F :=
    fun _ hx => birthEssentialSet_subset F T r birth
      (essentialBirthFiber_subset F T r birth t hx)
  have points : essentialBirthFiber F T r birth t ⊆ L := fun _ hx => filter.subset (positive hx)
  cases layer with
  | countablePoints D _ small cover =>
    have subset : essentialBirthFiber F T r birth t ⊆ D := by
      intro x hx
      exact cover x (points hx) ((mem_essentialBirthFiber F T r birth t x).1 hx).2.2
    have countableFiber := M.groundEmbeddable_restrict separation groundFiber
      (M.omega_mem separation infinite) subset small
    exact M.internalCountableBelow_of_countable groundFiber countableFiber positive
      (fun x hx => meet.order.refl x (points hx))
  | copies I parts groundI small groundParts index e previous groundCopy embedding cover inCopy =>
    apply M.internalCountableBelow_indexed_union pairing unions powers separation infinite choice
      groundI hr hF groundFiber groundParts small
    · intro x hx
      exact cover x (points hx) ((mem_essentialBirthFiber F T r birth t x).1 hx).2.2
    · intro i hi
      obtain ⟨groundA, source, sourceBases⟩ := earlier (index i) (previous i hi)
      have basis := M.internalCountableBelow_copy_of_all_filters pairing unions powers separation
        infinite groundA hL (groundCopy i hi) hF source filter (embedding i hi) sourceBases
      apply basis.mono
      intro x hx
      obtain ⟨hxFiber, part⟩ := (mem_relationFiber (essentialBirthFiber F T r birth t) parts i x).1 hx
      exact ZFSet.mem_inter.2 ⟨positive hxFiber, inCopy i hi x (points hxFiber) part⟩
  | separated I index e previous groundCopy embedding component cover separated =>
    by_cases inhabited : (essentialBirthFiber F T r birth t).Nonempty
    · obtain ⟨x, hx⟩ := inhabited
      let representative : {x : ZFSet.{u} // x ∈ L ∧ ZFSet.pair x t ∈ birth} :=
        ⟨x, points hx, ((mem_essentialBirthFiber F T r birth t x).1 hx).2.2⟩
      let i := component representative
      obtain ⟨groundA, source, sourceBases⟩ := earlier (index i) (previous i)
      have basis := M.internalCountableBelow_copy_of_all_filters pairing unions powers separation
        infinite groundA hL (groundCopy i) hF source filter (embedding i) sourceBases
      apply basis.mono
      intro y hy
      let current : {x : ZFSet.{u} // x ∈ L ∧ ZFSet.pair x t ∈ birth} :=
        ⟨y, points hy, ((mem_essentialBirthFiber F T r birth t y).1 hy).2.2⟩
      have same : component current = i := by
        by_contra different
        exact birthEssentials_no_oldBridge meet filter born
          (essentialBirthFiber_subset F T r birth t hy)
          (essentialBirthFiber_subset F T r birth t hx)
          current.property.2 representative.property.2 (separated current representative different)
      have inside := cover current
      rw [same] at inside
      exact ZFSet.mem_inter.2 ⟨positive hy, inside⟩
    · have empty : essentialBirthFiber F T r birth t = ∅ := by
        apply ZFSet.ext
        intro x
        exact ⟨fun hx => False.elim (inhabited ⟨x, hx⟩),
          fun hx => False.elim (ZFSet.notMem_empty x hx)⟩
      rw [empty]
      exact M.internalCountableBelow_empty ⟨F, hF⟩ r F

end CodedGrowthLayer

end

namespace CodedGrowthLayer

universe u

def of_inclusion {M N : TransitiveGround.{u}}
    {Space sourceOrder sourceMeet : ZFSet.{u} → ZFSet.{u}}
    {L r μ birth t : ZFSet.{u}}
    (layer : CodedGrowthLayer M Space sourceOrder sourceMeet L r μ birth t)
    (includes : M.sets ⊆ N.sets) :
    CodedGrowthLayer N Space sourceOrder sourceMeet L r μ birth t := by
  cases layer with
  | countablePoints D ground small cover =>
    exact .countablePoints D (includes ground)
      (M.groundEmbeddable_of_inclusion N includes small) cover
  | copies I parts groundI small groundParts index e earlier groundCopy embedding cover inCopy =>
    exact .copies I parts (includes groundI)
      (M.groundEmbeddable_of_inclusion N includes small) (includes groundParts)
      index e earlier (fun i hi => includes (groundCopy i hi)) embedding cover inCopy
  | separated I index e earlier groundCopy embedding component cover separated =>
    exact .separated I index e earlier (fun i => includes (groundCopy i))
      embedding component cover separated

def congr_sources_below {M : TransitiveGround.{u}}
    {Space sourceOrder sourceMeet Space' sourceOrder' sourceMeet' : ZFSet.{u} → ZFSet.{u}}
    {L r μ birth t : ZFSet.{u}}
    (layer : CodedGrowthLayer M Space sourceOrder sourceMeet L r μ birth t)
    (spaces : ∀ s ∈ t, Space s = Space' s)
    (orders : ∀ s ∈ t, sourceOrder s = sourceOrder' s)
    (meets : ∀ s ∈ t, sourceMeet s = sourceMeet' s) :
    CodedGrowthLayer M Space' sourceOrder' sourceMeet' L r μ birth t := by
  cases layer with
  | countablePoints D ground small cover =>
    exact .countablePoints D ground small cover
  | copies I parts groundI small groundParts index e earlier groundCopy embedding cover inCopy =>
    refine .copies I parts groundI small groundParts index e earlier groundCopy ?_ cover ?_
    · intro i hi
      simpa only [← spaces (index i) (earlier i hi), ← orders (index i) (earlier i hi),
        ← meets (index i) (earlier i hi)] using embedding i hi
    · intro i hi x hx entry
      simpa only [← spaces (index i) (earlier i hi)] using inCopy i hi x hx entry
  | separated I index e earlier groundCopy embedding component cover separation =>
    refine .separated I index e earlier groundCopy ?_ component ?_ separation
    · intro i
      simpa only [← spaces (index i) (earlier i), ← orders (index i) (earlier i),
        ← meets (index i) (earlier i)] using embedding i
    · intro x
      simpa only [← spaces (index (component x)) (earlier (component x))] using cover x

end CodedGrowthLayer

end PartitionPilot.Forcing

end OAI
