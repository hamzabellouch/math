import OAI.SetTheory.PartitionPrinciple.Geometry.GroundBelowInitialCompression

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem orderedPairNameFamily_below
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {one X Y K : ZFSet.{u}}
    (hone : one ∈ M.sets) (hX : X ∈ M.sets) (hY : Y ∈ M.sets) (hK : K ∈ M.sets)
    (standard : GroundStandardInaccessible M K)
    (smallX : GroundBelow M X K) (smallY : GroundBelow M Y K) :
    GroundBelow M (orderedPairNameFamily one X Y) K := by
  obtain ⟨ordinal, omega, regular, strong⟩ := standard.to_conditions pairing unions powers separation hK
  have hSingleton : ({one} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hone hone
  have singletonSmall := GroundBelow.singleton pairing unions powers separation infinite hK omega hone
  have hUnion := M.binary_union_mem pairing unions hX hY
  have unionSmall := GroundBelow.binary_union pairing unions powers separation infinite choice
    hX hY hK omega ordinal regular strong smallX smallY
  have hFirst := M.prod_mem pairing unions powers separation hUnion hSingleton
  have firstSmall := GroundBelow.product pairing unions powers separation hUnion hSingleton hK
    ordinal strong unionSmall singletonSmall
  have hPower := M.groundPower_mem powers hFirst
  have powerSmall := strong.power_closed pairing unions powers separation hFirst hK firstSmall
  have hSecond := M.prod_mem pairing unions powers separation hPower hSingleton
  have secondSmall := GroundBelow.product pairing unions powers separation hPower hSingleton hK
    ordinal strong powerSmall singletonSmall
  have boundSmall := strong.power_closed pairing unions powers separation hSecond hK secondSmall
  exact boundSmall.restrict separation
    (M.orderedPairNameFamily_mem pairing unions powers separation hone hX hY) hK
    (M.orderedPairNameFamily_subset_bound pairing hone hX hY)

theorem iteratedPairNameFamily_below
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {one T K : ZFSet.{u}}
    (hone : one ∈ M.sets) (hT : T ∈ M.sets) (hK : K ∈ M.sets)
    (standard : GroundStandardInaccessible M K) (small : GroundBelow M T K) (n : Nat) :
    GroundBelow M (iteratedPairNameFamily one T n) K := by
  induction n with
  | zero => exact small
  | succ n ih =>
      exact M.orderedPairNameFamily_below pairing unions powers separation infinite choice hone
        (M.iteratedPairNameFamily_mem pairing unions powers separation hone hT n) hT hK standard ih small

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization Compression.RecursiveMaps
universe u v
variable (M : TransitiveGround.{u}) {P : Type u} [PartialOrder P] [OrderTop P]
variable {G : Type v} [Group G] (a : PosetAction G P) (s : Presentation P)
variable (F : NormalSubgroupFamily G)

theorem invariantNamePowers
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {T K : ZFSet.{u}} (hone : s.encode ⊤ ∈ M.sets)
    (hT : T ∈ M.sets) (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (small : GroundBelow M T K) (valid : ∀ z ∈ T, IsName s z)
    (closed : ∀ g (τ : Name s), τ.val ∈ T → (a.act s g τ).val ∈ T)
    (children : ∀ τ : Name s, τ.val ∈ T → HereditarilySymmetric a s F τ) :
    ∀ n : Nat, let terms := iteratedPairNameFamily (s.encode ⊤) T n
      terms ∈ M.sets ∧ GroundBelow M terms K ∧
      (∀ z ∈ terms, IsName s z) ∧
      (∀ σ : Name s, σ.val ∈ terms → HereditarilySymmetric a s F σ) ∧
      ∃ τ : Name s, τ.val ∈ M.sets ∧ τ.val = ZFSet.prod terms {s.encode ⊤} ∧
        HereditarilySymmetric a s F τ ∧ (∀ g, a.act s g τ = τ) ∧
        ∀ H : Set P, ⊤ ∈ H → ∀ x,
          x ∈ Name.eval H τ ↔ ∃ σ : Name s, σ.val ∈ terms ∧ Name.eval H σ = x := by
  intro n
  let terms := iteratedPairNameFamily (s.encode ⊤) T n
  have hTerms := M.iteratedPairNameFamily_mem pairing unions powers separation hone hT n
  have typed := iteratedPairNameFamily_valid (s := s) ⊤ valid n
  refine ⟨hTerms, M.iteratedPairNameFamily_below pairing unions powers separation infinite choice
    hone hT hK standard small n, typed, iteratedPairNameFamily_hs a F valid children n,
    Name.familySet ⊤ terms typed,
    M.familySet_mem s ⊤ pairing unions powers separation hTerms hone typed,
    Name.familySet_code ⊤ terms typed,
    iteratedPairNameFamilySet_hs a F valid closed children n,
    iteratedPairNameFamilySet_invariant a valid closed n, ?_⟩
  intro H top x
  exact Name.mem_eval_familySet H ⊤ top terms typed x

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
