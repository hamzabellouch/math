import OAI.SetTheory.PartitionPrinciple.Forcing.GroundBinaryRowNames

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem completeProjection_codedGeneric_of_ordinary
    {Upper Lower : Type u} [PartialOrder Upper] [PartialOrder Lower]
    (upper : Presentation Upper) (lower : Presentation Lower)
    {restriction : Upper →o Lower} {inclusion : Lower ↪o Upper}
    (projection : CompleteProjection restriction inclusion)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (upperCarrier : upper.carrier ∈ M.sets) (lowerCarrier : lower.carrier ∈ M.sets)
    (restrictionGround : upper.graph lower restriction ∈ M.sets)
    (H : ConditionFilter Upper)
    (ordinary : H.GenericFor (formulaFamily (M.nameDomain upper))) :
    (projection.projectedFilter H).GenericFor (M.codedFamily lower) := by
  intro E member dense
  obtain ⟨X, ground, rfl⟩ := member
  have preimage := M.presentedPreimage_mem upper lower restriction
    pairing unions powers separation upperCarrier lowerCarrier restrictionGround ground
  exact (projection.projectedFilter_meets_iff H _).2
    (M.ordinary_generic_meets_coded_dense upper pairing unions powers separation
      H ordinary preimage (projection.dense_preimage dense))

theorem completeProjection_binaryRowValues_ne
    {Upper : Type u} [PartialOrder Upper] (upper : Presentation Upper)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {I C : ZFSet.{u}} (hI : I ∈ M.sets) (hC : C ∈ M.sets)
    (uncountable : ¬ M.groundEmbeddable C ZFSet.omega)
    (upperCarrier : upper.carrier ∈ M.sets) :
    let R := M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega
    letI := M.smallFunctionOrder (ZFSet.prod I C) (natSetCode 2) ZFSet.omega
    let lower := SetMembers.presentation R
    ∀ (restriction : Upper →o SetMembers R) (inclusion : SetMembers R ↪o Upper)
      (_projection : CompleteProjection restriction inclusion),
      upper.graph lower restriction ∈ M.sets →
      ∀ (H : ConditionFilter Upper),
        H.GenericFor (formulaFamily (M.nameDomain upper)) →
        ∀ (one : SetMembers R), H.mem (inclusion one) →
        ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
          Name.eval {p | H.mem p}
            (Name.rename upper inclusion (M.binaryRowName I C one i)) ≠
          Name.eval {p | H.mem p}
            (Name.rename upper inclusion (M.binaryRowName I C one j)) := by
  let R := M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionOrder (ZFSet.prod I C) (natSetCode 2) ZFSet.omega
  let lower := SetMembers.presentation R
  dsimp only
  intro restriction inclusion projection restrictionGround H ordinary one hone i hi j hj distinct
  have lowerCarrier : lower.carrier ∈ M.sets :=
    M.countablePartialFunctions_mem pairing unions powers separation infinite
      (M.prod_mem pairing unions powers separation hI hC)
      (M.natSetCode_mem separation infinite 2)
  have generic := M.completeProjection_codedGeneric_of_ordinary upper lower projection
    pairing unions powers separation upperCarrier lowerCarrier restrictionGround H ordinary
  have hone' : (projection.projectedFilter H).mem one := hone
  intro equal
  have same : Name.eval {p | (projection.projectedFilter H).mem p} (M.binaryRowName I C one i) =
      Name.eval {p | (projection.projectedFilter H).mem p} (M.binaryRowName I C one j) := by
    simpa only [Name.eval_rename, CompleteProjection.projectedFilter, Set.mem_ofPred_eq] using equal
  rw [M.eval_binaryRowName I C one (projection.projectedFilter H) hone',
    M.eval_binaryRowName I C one (projection.projectedFilter H) hone'] at same
  exact M.binaryGenericRow_ne pairing unions powers separation infinite choice
    hI hC hi hj distinct uncountable (projection.projectedFilter H) generic same

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u})

theorem projectedBinaryRows_uniqueFiber_incompatible
    {Upper G : Type u} [PartialOrder Upper] [Group G]
    (upper : Presentation Upper) (t : Presentation G)
    (a : PosetAction G Upper) (F : NormalSubgroupFamily G)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (small : M.sets.Countable)
    {I C : ZFSet.{u}} (hI : I ∈ M.sets) (hC : C ∈ M.sets)
    (uncountable : ¬ M.groundEmbeddable C ZFSet.omega)
    (upperCarrier : (upper).carrier ∈ M.sets)
    (maps : a.conditionMapFamily upper t ∈ M.sets) :
    let R := M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega
    letI := M.smallFunctionOrder (ZFSet.prod I C) (natSetCode 2) ZFSet.omega
    let lower := SetMembers.presentation R
    ∀ (restriction : Upper →o SetMembers R) (inclusion : SetMembers R ↪o Upper)
      (_projection : CompleteProjection restriction inclusion),
      (upper).graph lower restriction ∈ M.sets →
      ∀ (one : SetMembers R), (∀ q : SetMembers R, q ≤ one) →
      ∀ (S x f : (M.nameDomain upper).names) (g : G),
        a.act upper g S.val = S.val → a.act upper g f.val = f.val →
        ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
          x.val = Name.rename upper inclusion (M.binaryRowName I C one i) →
          a.act upper g x.val = Name.rename upper inclusion (M.binaryRowName I C one j) →
          ∀ p : Upper,
            Forces (M.nameDomain upper) (BoundedFormula.uniqueFiberFormula 0 1 2).toFormula
              (extend S (extend x (extend f Fin.elim0))) p →
            ¬ Compatible p (a.iso g p) := by
  let R := M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionOrder (ZFSet.prod I C) (natSetCode 2) ZFSet.omega
  let lower := SetMembers.presentation R
  dsimp only
  intro restriction inclusion projection restrictionGround one greatest S x f g fixedS fixedF
    i hi j hj distinct originalRow movedRow p forced compatible
  obtain ⟨r, rp, rgp⟩ := compatible
  obtain ⟨H, hr, _coded, ordinary, _symmetric⟩ :=
    M.exists_joint_generic upper a F small upperCarrier r
  have closed : ∀ g tau, tau ∈ (M.nameDomain upper).names →
      a.act upper g tau ∈ (M.nameDomain upper).names :=
    M.act_mem upper a t pairing unions powers separation collection upperCarrier maps
  have equal := a.uniqueFiber_eq_of_fixed_names upper (M.nameDomain upper) closed
    g S x f fixedS fixedF p forced H ordinary (H.upward hr rp) (H.upward hr rgp)
  rw [movedRow, originalRow] at equal
  have hone : H.mem (inclusion one) :=
    H.upward hr ((projection.le_include_iff r one).2 (greatest (restriction r)))
  exact M.completeProjection_binaryRowValues_ne upper pairing unions powers separation infinite
    choice hI hC uncountable upperCarrier restriction inclusion projection restrictionGround
    H ordinary one hone i hi j hj distinct equal

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
