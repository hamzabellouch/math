import OAI.SetTheory.PartitionPrinciple.Forcing.GroundGraphValueDescendantWitnesses

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P Q : Type u}

theorem rename_between_mem (s : Presentation P) (t : Presentation Q)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (hs : s.carrier ∈ M.sets) (ht : t.carrier ∈ M.sets)
    (f : P → Q) (hf : s.graph t f ∈ M.sets)
    (τ : Name s) (hτ : τ.val ∈ M.sets) : (Name.rename t f τ).val ∈ M.sets := by
  let U := s.carrier ∪ t.carrier
  let D := ZFSet.sep (fun x => x ∉ s.carrier) U
  let F := s.graph t f
  let G := F ∪ identityFunctionGraph D
  have subS : s.carrier ⊆ U := fun _ hx => ZFSet.mem_union.2 (Or.inl hx)
  have subT : t.carrier ⊆ U := fun _ hx => ZFSet.mem_union.2 (Or.inr hx)
  have hU : U ∈ M.sets := M.binary_union_mem pairing unions hs ht
  have hD : D ∈ M.sets := M.bounded_separation_mem separation (.neg (.mem 0 1))
    (extend s.carrier Fin.elim0) (Fin.cases hs (fun i => Fin.elim0 i)) hU
  have hG : G ∈ M.sets := M.binary_union_mem pairing unions hf
    (M.identityFunctionGraph_mem pairing unions powers separation hD)
  have ff := s.graph_isFunc t f
  have full : ZFSet.IsFunc U U G := by
    constructor
    · intro z hz
      rcases ZFSet.mem_union.1 hz with old | identity
      · obtain ⟨x, hx, y, hy, eq⟩ := ZFSet.mem_prod.1 (ff.1 old)
        exact ZFSet.mem_prod.2 ⟨x, subS hx, y, subT hy, eq⟩
      · obtain ⟨x, hx, rfl⟩ := (mem_identityFunctionGraph D z).1 identity
        exact ZFSet.pair_mem_prod.2 ⟨(ZFSet.mem_sep.1 hx).1, (ZFSet.mem_sep.1 hx).1⟩
    · intro x hx
      by_cases source : x ∈ s.carrier
      · obtain ⟨y, entry, unique⟩ := ff.2 x source
        refine ⟨y, ZFSet.mem_union.2 (Or.inl entry), ?_⟩
        intro z hz
        rcases ZFSet.mem_union.1 hz with old | identity
        · exact unique z old
        · exact False.elim ((ZFSet.mem_sep.1
            ((pair_mem_identityFunctionGraph D x z).1 identity).2).2 source)
      · refine ⟨x, ZFSet.mem_union.2 (Or.inr
          ((pair_mem_identityFunctionGraph D x x).2 ⟨rfl, ZFSet.mem_sep.2 ⟨hx, source⟩⟩)), ?_⟩
        intro z hz
        rcases ZFSet.mem_union.1 hz with old | identity
        · exact False.elim (source (ZFSet.pair_mem_prod.1 (ff.1 old)).1)
        · exact ((pair_mem_identityFunctionGraph D x z).1 identity).1.symm
  let u := SetMembers.presentation U
  let es := s.intoSet U subS
  let et := t.intoSet U subT
  let h := u.decodeFunction u G full
  have commute (p : P) : h (es p) = et (f p) := by
    apply (u.decodeFunction_iff u G full (es p) (et (f p))).2
    rw [s.encode_intoSet U subS, t.encode_intoSet U subT]
    exact ZFSet.mem_union.2 (Or.inl ((s.pair_mem_graph t f p (f p)).2 rfl))
  have sourceCode := Name.rename_val_of_encode u es (s.encode_intoSet U subS) τ
  have ground := M.rename_mem u pairing unions powers separation collection hU h
    ((u.graph_decodeFunction u G full).symm ▸ hG)
    (Name.rename u es τ) (sourceCode ▸ hτ)
  have equation : Name.rename u h (Name.rename u es τ) =
      Name.rename u et (Name.rename t f τ) := by
    rw [Name.rename_comp, Name.rename_comp]
    apply congrArg (fun k => Name.rename u k τ)
    funext p
    exact commute p
  rw [equation, Name.rename_val_of_encode u et (t.encode_intoSet U subT)] at ground
  exact ground

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {Lower Upper : Type u}
variable [PartialOrder Lower] [PartialOrder Upper]
variable (lower : Presentation Lower) (upper : Presentation Upper)
variable {restriction : Upper →o Lower} {inclusion : Lower ↪o Upper}
variable (projection : CompleteProjection restriction inclusion)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0)
variable (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
variable (lowerGround : lower.carrier ∈ M.sets) (upperGround : upper.carrier ∈ M.sets)
variable (inclusionGround : lower.graph upper inclusion ∈ M.sets)
variable (H : ConditionFilter Upper)
variable (ordinary : H.GenericFor (formulaFamily (M.nameDomain upper)))
include pairing unions powers separation collection lowerGround upperGround inclusionGround ordinary

theorem completeProjection_eval_eq_iff_forcesEq (sigma tau : Name lower)
    (sigmaGround : sigma.val ∈ M.sets) (tauGround : tau.val ∈ M.sets) :
    Name.eval {q | (projection.projectedFilter H).mem q} sigma =
      Name.eval {q | (projection.projectedFilter H).mem q} tau ↔
    ∃ q, (projection.projectedFilter H).mem q ∧ Name.ForcesEq q sigma tau := by
  have liftedSigma := M.rename_between_mem lower upper pairing unions powers separation collection
    lowerGround upperGround inclusion inclusionGround sigma sigmaGround
  have liftedTau := M.rename_between_mem lower upper pairing unions powers separation collection
    lowerGround upperGround inclusion inclusionGround tau tauGround
  have truth := Name.eval_eq_iff_forcesEq (M.nameDomain upper) H
    (fun E member => ordinary E (Or.inl member)) liftedSigma liftedTau
  simp only [Name.eval_rename] at truth
  constructor
  · intro equal
    obtain ⟨p, member, forced⟩ := truth.1 equal
    exact ⟨restriction p, (projection.projectedFilter_mem_iff H _).2 ⟨p, member, rfl⟩,
      (Name.forcesEq_rename_completeProjection lower upper restriction inclusion projection p sigma tau).1 forced⟩
  · rintro ⟨q, member, forced⟩
    apply truth.2
    refine ⟨inclusion q, member, ?_⟩
    apply (Name.forcesEq_rename_completeProjection lower upper restriction inclusion projection
      (inclusion q) sigma tau).2
    simpa only [projection.retract] using forced

theorem completeProjection_eval_mem_iff_forcesMem (sigma tau : Name lower)
    (sigmaGround : sigma.val ∈ M.sets) (tauGround : tau.val ∈ M.sets) :
    Name.eval {q | (projection.projectedFilter H).mem q} sigma ∈
      Name.eval {q | (projection.projectedFilter H).mem q} tau ↔
    ∃ q, (projection.projectedFilter H).mem q ∧ Name.ForcesMem q sigma tau := by
  have liftedSigma := M.rename_between_mem lower upper pairing unions powers separation collection
    lowerGround upperGround inclusion inclusionGround sigma sigmaGround
  have liftedTau := M.rename_between_mem lower upper pairing unions powers separation collection
    lowerGround upperGround inclusion inclusionGround tau tauGround
  have truth := Name.eval_mem_iff_forcesMem (M.nameDomain upper) H
    (fun E member => ordinary E (Or.inl member)) liftedSigma liftedTau
  simp only [Name.eval_rename] at truth
  constructor
  · intro member
    obtain ⟨p, hp, forced⟩ := truth.1 member
    exact ⟨restriction p, (projection.projectedFilter_mem_iff H _).2 ⟨p, hp, rfl⟩,
      (Name.forcesMem_rename_completeProjection lower upper restriction inclusion projection p sigma tau).1 forced⟩
  · rintro ⟨q, member, forced⟩
    apply truth.2
    refine ⟨inclusion q, member, ?_⟩
    apply (Name.forcesMem_rename_completeProjection lower upper restriction inclusion projection
      (inclusion q) sigma tau).2
    simpa only [projection.retract] using forced

theorem completeProjection_forcesNotEq_sound (sigma tau : Name lower)
    (sigmaGround : sigma.val ∈ M.sets) (tauGround : tau.val ∈ M.sets)
    {q : Lower} (member : (projection.projectedFilter H).mem q)
    (negative : ∀ r, r ≤ q → ¬ Name.ForcesEq r sigma tau) :
    Name.eval {r | (projection.projectedFilter H).mem r} sigma ≠
      Name.eval {r | (projection.projectedFilter H).mem r} tau := by
  intro equal
  obtain ⟨r, hr, forced⟩ := (M.completeProjection_eval_eq_iff_forcesEq lower upper projection
    pairing unions powers separation collection lowerGround upperGround inclusionGround H ordinary
    sigma tau sigmaGround tauGround).1 equal
  obtain ⟨p, _hp, pq, pr⟩ := (projection.projectedFilter H).directed member hr
  exact negative p pq (Name.forcesEq_mono forced pr)

theorem completeProjection_forcesNotMem_sound (sigma tau : Name lower)
    (sigmaGround : sigma.val ∈ M.sets) (tauGround : tau.val ∈ M.sets)
    {q : Lower} (member : (projection.projectedFilter H).mem q)
    (negative : Name.ForcesNotMem q sigma tau) :
    Name.eval {r | (projection.projectedFilter H).mem r} sigma ∉
      Name.eval {r | (projection.projectedFilter H).mem r} tau := by
  intro belongs
  obtain ⟨r, hr, forced⟩ := (M.completeProjection_eval_mem_iff_forcesMem lower upper projection
    pairing unions powers separation collection lowerGround upperGround inclusionGround H ordinary
    sigma tau sigmaGround tauGround).1 belongs
  obtain ⟨p, _hp, pq, pr⟩ := (projection.projectedFilter H).directed member hr
  exact negative p pq (Name.forcesMem_mono forced pr)

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
