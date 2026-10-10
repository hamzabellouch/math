import OAI.SetTheory.PartitionPrinciple.Forcing.GroundSupportedCertificateFamilyDecisions
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundSupportedCertificateProfiles
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundCertificateProfileImageFamilies

namespace OAI

namespace PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment
open SetFormula SetRealization
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {level : GroundMainCandidateLevel M K} {i₀ : I}
variable (fulfilled : run.FinalSupportFulfillment level i₀)
variable {Q : Type u} [PartialOrder Q] [OrderTop Q] (s : Presentation Q)

theorem exists_forcedSupportedCertificateFamily
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (small : M.sets.Countable) (closed : InternallyCountablyClosed M s)
    (smallD : M.groundEmbeddable D ZFSet.omega)
    (irreflexive : ∀ q ∈ D, ZFSet.pair q q ∉ rD) :
    let geometry := run.finalGeometry i₀
    letI := geometry.group_code.toGroup
    letI := geometry.meet.order.toPartialOrder
    letI := geometry.decodedBottom
    let b := SetMembers.presentation geometry.carrier
    let t := SetMembers.presentation geometry.actors
    let d := geometry.decodedAction
    let directed := geometry.decoded_directed fulfilled.directed
    ∀ (a : PosetAction (SetMembers geometry.actors) Q)
      (_maps : a.conditionMapFamily s t ∈ M.sets)
      (T : ZFSet.{u}) (_hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
      (_terms : ∀ g (τ : Name s), τ.val ∈ T → (a.act s g τ).val ∈ T)
      (_children : ∀ τ : Name s, τ.val ∈ T →
        HereditarilySymmetric a s (d.principalSupportFamily ⊥ directed) τ)
      (H : ConditionFilter Q) (_genericCoded : H.GenericFor (M.codedFamily s))
      (_genericFormula : H.GenericFor (formulaFamily (M.nameDomain s)))
      (_descent : ∀ (v w : SetMembers geometry.carrier) (x y : (M.nameDomain s).names),
        d.principalFix v ≤ a.stabilizer s x.val →
        d.principalFix w ≤ a.stabilizer s y.val →
        HereditarilySymmetric a s (d.principalSupportFamily ⊥ directed) x.val →
        HereditarilySymmetric a s (d.principalSupportFamily ⊥ directed) y.val →
        Name.eval {p | H.mem p} x.val = Name.eval {p | H.mem p} y.val →
        ∃ τ : (M.nameDomain s).names,
          HereditarilySymmetric a s (d.principalSupportFamily ⊥ directed) τ.val ∧
          d.principalFix (geometry.meet.smallMeet v w) ≤ a.stabilizer s τ.val ∧
          Name.eval {p | H.mem p} τ.val = Name.eval {p | H.mem p} x.val)
      (J : ZFSet.{u}) (_hJ : J ∈ M.sets) (validJ : ∀ z ∈ J, IsName s z)
      (_smallJ : M.groundEmbeddable J ZFSet.omega)
      (_hs : ∀ z : Name s, z.val ∈ J →
        HereditarilySymmetric a s (d.principalSupportFamily ⊥ directed) z)
      (_subset : ∀ z : Name s, z.val ∈ J → Name.eval {p | H.mem p} z ⊆
        Name.eval {p | H.mem p} (Name.familySet ⊤ T valid))
      (p : Q) (_hp : H.mem p),
      ∃ (k : ZFSet.{u}) (hk : k ∈ M.sets),
        ZFSet.IsFunc J (M.supportedEqualityCertificateBound b.carrier
          (M.niceSupportNameCodes a s T d.principalFix)) k ∧
        k ⊆ M.supportedCertificateFamilyRelation a s b T d.principalFix
          geometry.order J validJ H ∧
        ∃ q, H.mem q ∧ q ≤ p ∧
          Forces (M.nameDomain s) supportedCertificateFamilyFormula
            (M.supportedCertificateFamilyEnv a s t b T d.principalFix pairing unions powers
              separation collection carrier geometry.actors_ground geometry.carrier_ground
              (geometry.decoded_supportBasis_ground pairing unions powers separation)
              _maps _hT valid (M.omega_mem separation infinite) geometry.order J k
              geometry.order_ground _hJ hk validJ) q ∧
          ∀ (z : (M.nameDomain s).names) (F B f : ZFSet.{u}),
            ZFSet.pair z.val.val (ZFSet.pair F (ZFSet.pair B f)) ∈ k →
            F = M.visibleSupportProfile a s b d T H (Name.eval {p | H.mem p} z.val) ∧
            MeetFilterCode geometry.carrier geometry.order geometry.meetGraph F ∧
            B.Nonempty ∧ M.DecidesVisibilityProfile a s b d.principalFix T F z.val q ∧
            (∀ v ∈ B, ∀ tau : Name s, tau.val ∈ M.niceSupportNameCodes a s T d.principalFix →
              ZFSet.pair v tau.val ∈ f → Name.ForcesEq q z.val tau) ∧
            ∃ e ∈ M.sets, ∃ names ∈ M.sets,
              ZFSet.IsFunc ZFSet.omega B e ∧
              ZFSet.IsFunc ZFSet.omega (M.niceSupportNameCodes a s T d.principalFix) names ∧
              (∀ v ∈ B, ∃ n ∈ ZFSet.omega, ZFSet.pair n v ∈ e) ∧
              (∀ n ∈ ZFSet.omega, ∀ v tau, ZFSet.pair n v ∈ e →
                ZFSet.pair n tau ∈ names → ZFSet.pair v tau ∈ f) ∧
              (∀ n ∈ ZFSet.omega, ∀ v tau, ZFSet.pair n v ∈ e →
                ZFSet.pair v tau ∈ f → ZFSet.pair n tau ∈ names) := by
  let geometry := run.finalGeometry i₀
  let := geometry.group_code.toGroup
  let := geometry.meet.order.toPartialOrder
  let := geometry.decodedBottom
  let b := SetMembers.presentation geometry.carrier
  let t := SetMembers.presentation geometry.actors
  let d := geometry.decodedAction
  let directed := geometry.decoded_directed fulfilled.directed
  dsimp only
  intro a maps T hT valid terms children H genericCoded genericFormula descent
    J hJ validJ smallJ hs subsets p hp
  have supports := geometry.decoded_supportBasis_ground pairing unions powers separation
  have omega := M.omega_mem separation infinite
  have codesGround := M.niceSupportNameCodes_mem a s b T d.principalFix t pairing unions powers
    separation collection carrier geometry.actors_ground geometry.carrier_ground supports maps hT valid
  obtain ⟨k, hk, function, selected⟩ := fulfilled.exists_supportedCertificateFamily s collection
    infinite choice carrier order small closed smallD irreflexive a maps T hT valid terms children
    H genericCoded genericFormula descent J hJ validJ smallJ hs subsets
  obtain ⟨q, hq, qp, forced⟩ := M.exists_forced_supportedCertificateFamily a s t b T d.principalFix
    pairing unions powers separation collection carrier geometry.actors_ground geometry.carrier_ground
    supports maps hT valid omega geometry.order J k geometry.order_ground hJ hk validJ H
    genericFormula selected p hp
  refine ⟨k, hk, function, selected, q, hq, qp, forced, ?_⟩
  intro z F B f entry
  have bound := ZFSet.pair_mem_prod.1 (function.1 entry)
  have fields := (M.mem_supportedEqualityCertificateBound b.carrier
    (M.niceSupportNameCodes a s T d.principalFix) F B f).1 bound.2
  obtain ⟨_, _, _, _, value, evaluated, certificate⟩ :=
    (pair_mem_supportedCertificateRelation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).1 (selected entry)
  have valueEqual := (Name.inputEvaluationName_entry s J validJ z.val H value).1 evaluated
  have actual : SupportedEqualityCertificate b.carrier
      (M.niceSupportNameCodes a s T d.principalFix) geometry.order
      (M.niceSupportRelation a s b T d.principalFix)
      (Name.eval {p | H.mem p} (M.niceSupportEvaluationName a s T d.principalFix))
      (Name.eval {p | H.mem p} (M.niceVisibilityEvaluationName a s b T d.principalFix))
      (Name.eval {p | H.mem p} z.val) F B f := valueEqual.2.symm ▸ certificate
  have profileEqual := M.supportedCertificate_profile_eq a s b d T H actual
  obtain ⟨_, profileFilter, _⟩ := fulfilled.exists_decided_visibilityProfile s collection infinite
    choice carrier order small closed smallD irreflexive a maps T hT valid terms children
    H genericCoded genericFormula descent z (hs z.val bound.1) (subsets z.val bound.1) p hp
  have filter : MeetFilterCode geometry.carrier geometry.order geometry.meetGraph F :=
    profileEqual.symm ▸ profileFilter
  have nonempty := actual.basis_nonempty filter.nonempty
  have decisions := M.forces_supportedCertificateFamily_profile a s t b T d.principalFix
    pairing unions powers separation collection carrier geometry.actors_ground geometry.carrier_ground
    supports maps hT valid omega geometry.order J k geometry.order_ground hJ hk validJ small
    z F B f q forced entry fields.1.1
  refine ⟨profileEqual, filter, nonempty, decisions, ?_, ?_⟩
  · intro v hv tau ht selectedEntry
    exact M.forces_supportedCertificateFamily_equality a s t b T d.principalFix pairing unions powers
      separation collection carrier geometry.actors_ground geometry.carrier_ground supports maps hT valid
      omega geometry.order J k geometry.order_ground hJ hk validJ small z F B f q forced entry
      v hv tau ht selectedEntry
  · exact M.groundFunction_enumeration pairing unions powers separation infinite fields.2.1.1
      codesGround fields.2.2.1 nonempty fields.2.1.2.2 actual.2.2.2.1

theorem exists_enumeratedSupportedCertificateFamily
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (small : M.sets.Countable) (closed : InternallyCountablyClosed M s)
    (smallD : M.groundEmbeddable D ZFSet.omega)
    (irreflexive : ∀ q ∈ D, ZFSet.pair q q ∉ rD) :
    let geometry := run.finalGeometry i₀
    letI := geometry.group_code.toGroup
    letI := geometry.meet.order.toPartialOrder
    letI := geometry.decodedBottom
    let b := SetMembers.presentation geometry.carrier
    let t := SetMembers.presentation geometry.actors
    let d := geometry.decodedAction
    let directed := geometry.decoded_directed fulfilled.directed
    ∀ (a : PosetAction (SetMembers geometry.actors) Q)
      (_maps : a.conditionMapFamily s t ∈ M.sets)
      (T : ZFSet.{u}) (_hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
      (_terms : ∀ g (τ : Name s), τ.val ∈ T → (a.act s g τ).val ∈ T)
      (_children : ∀ τ : Name s, τ.val ∈ T →
        HereditarilySymmetric a s (d.principalSupportFamily ⊥ directed) τ)
      (H : ConditionFilter Q) (_genericCoded : H.GenericFor (M.codedFamily s))
      (_genericFormula : H.GenericFor (formulaFamily (M.nameDomain s)))
      (_descent : ∀ (v w : SetMembers geometry.carrier) (x y : (M.nameDomain s).names),
        d.principalFix v ≤ a.stabilizer s x.val →
        d.principalFix w ≤ a.stabilizer s y.val →
        HereditarilySymmetric a s (d.principalSupportFamily ⊥ directed) x.val →
        HereditarilySymmetric a s (d.principalSupportFamily ⊥ directed) y.val →
        Name.eval {p | H.mem p} x.val = Name.eval {p | H.mem p} y.val →
        ∃ τ : (M.nameDomain s).names,
          HereditarilySymmetric a s (d.principalSupportFamily ⊥ directed) τ.val ∧
          d.principalFix (geometry.meet.smallMeet v w) ≤ a.stabilizer s τ.val ∧
          Name.eval {p | H.mem p} τ.val = Name.eval {p | H.mem p} x.val)
      (J : ZFSet.{u}) (_hJ : J ∈ M.sets) (validJ : ∀ z ∈ J, IsName s z)
      (_smallJ : M.groundEmbeddable J ZFSet.omega)
      (_hs : ∀ z : Name s, z.val ∈ J →
        HereditarilySymmetric a s (d.principalSupportFamily ⊥ directed) z)
      (_subset : ∀ z : Name s, z.val ∈ J → Name.eval {p | H.mem p} z ⊆
        Name.eval {p | H.mem p} (Name.familySet ⊤ T valid))
      (p : Q) (_hp : H.mem p),
      ∃ (k : ZFSet.{u}) (hk : k ∈ M.sets),
        ZFSet.IsFunc J (M.supportedEqualityCertificateBound b.carrier
          (M.niceSupportNameCodes a s T d.principalFix)) k ∧
        k ⊆ M.supportedCertificateFamilyRelation a s b T d.principalFix
          geometry.order J validJ H ∧
        ∃ q, H.mem q ∧ q ≤ p ∧
          Forces (M.nameDomain s) supportedCertificateFamilyFormula
            (M.supportedCertificateFamilyEnv a s t b T d.principalFix pairing unions powers
              separation collection carrier geometry.actors_ground geometry.carrier_ground
              (geometry.decoded_supportBasis_ground pairing unions powers separation)
              _maps _hT valid (M.omega_mem separation infinite) geometry.order J k
              geometry.order_ground _hJ hk validJ) q ∧
          ∃ enumerations ∈ M.sets,
            ZFSet.IsFunc J (M.synchronizedEnumerationBound b.carrier
              (M.niceSupportNameCodes a s T d.principalFix)) enumerations ∧
            enumerations ⊆ M.certificateEnumerationRelation J b.carrier
              (M.niceSupportNameCodes a s T d.principalFix) k ∧
            (∀ j F B f e names,
              ZFSet.pair j (ZFSet.pair F (ZFSet.pair B f)) ∈ k →
              ZFSet.pair j (ZFSet.pair e names) ∈ enumerations →
              SynchronizedEnumerationCode ZFSet.omega
                (M.niceSupportNameCodes a s T d.principalFix) B f e names) ∧
            ∀ (z : (M.nameDomain s).names) (F B f : ZFSet.{u}),
              ZFSet.pair z.val.val (ZFSet.pair F (ZFSet.pair B f)) ∈ k →
              F = M.visibleSupportProfile a s b d T H (Name.eval {p | H.mem p} z.val) ∧
              MeetFilterCode geometry.carrier geometry.order geometry.meetGraph F ∧
              B.Nonempty ∧ M.DecidesVisibilityProfile a s b d.principalFix T F z.val q ∧
              (∀ v ∈ B, ∀ tau : Name s, tau.val ∈ M.niceSupportNameCodes a s T d.principalFix →
                ZFSet.pair v tau.val ∈ f → Name.ForcesEq q z.val tau) ∧
              ∃ e ∈ M.sets, ∃ names ∈ M.sets,
                ZFSet.IsFunc ZFSet.omega B e ∧
                ZFSet.IsFunc ZFSet.omega (M.niceSupportNameCodes a s T d.principalFix) names ∧
                (∀ v ∈ B, ∃ n ∈ ZFSet.omega, ZFSet.pair n v ∈ e) ∧
                (∀ n ∈ ZFSet.omega, ∀ v tau, ZFSet.pair n v ∈ e →
                  ZFSet.pair n tau ∈ names → ZFSet.pair v tau ∈ f) ∧
                (∀ n ∈ ZFSet.omega, ∀ v tau, ZFSet.pair n v ∈ e →
                  ZFSet.pair v tau ∈ f → ZFSet.pair n tau ∈ names) := by
  let geometry := run.finalGeometry i₀
  let := geometry.group_code.toGroup
  let := geometry.meet.order.toPartialOrder
  let := geometry.decodedBottom
  let b := SetMembers.presentation geometry.carrier
  let t := SetMembers.presentation geometry.actors
  let d := geometry.decodedAction
  let directed := geometry.decoded_directed fulfilled.directed
  dsimp only
  intro a maps T hT valid terms children H genericCoded genericFormula descent
    J hJ validJ smallJ hs subsets p hp
  obtain ⟨k, hk, function, selected, q, hq, qp, forced, entries⟩ :=
    fulfilled.exists_forcedSupportedCertificateFamily s collection infinite choice carrier order
      small closed smallD irreflexive a maps T hT valid terms children H genericCoded
      genericFormula descent J hJ validJ smallJ hs subsets p hp
  have supports := geometry.decoded_supportBasis_ground pairing unions powers separation
  have codesGround := M.niceSupportNameCodes_mem a s b T d.principalFix t pairing unions powers
    separation collection carrier geometry.actors_ground geometry.carrier_ground supports maps hT valid
  have certificates : ∀ j F B f, ZFSet.pair j (ZFSet.pair F (ZFSet.pair B f)) ∈ k →
      B.Nonempty ∧ ZFSet.IsFunc B (M.niceSupportNameCodes a s T d.principalFix) f := by
    intro j F B f stored
    have hj := (ZFSet.pair_mem_prod.1 (function.1 stored)).1
    let z : (M.nameDomain s).names := ⟨⟨j, validJ j hj⟩, M.transitive hJ hj⟩
    have chosen := entries z F B f stored
    obtain ⟨_, _, _, _, _, _, certificate⟩ :=
      (pair_mem_supportedCertificateRelation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).1 (selected stored)
    exact ⟨chosen.2.2.1, certificate.2.2.2.1⟩
  obtain ⟨enumerations, ground, enumerationFunction, enumerationRelation, synchronized⟩ :=
    M.exists_supportedCertificateEnumerations pairing unions powers separation infinite choice
      hJ geometry.carrier_ground codesGround hk function certificates
  exact ⟨k, hk, function, selected, q, hq, qp, forced, enumerations, ground,
    enumerationFunction, enumerationRelation, synchronized, entries⟩

end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment

end OAI
