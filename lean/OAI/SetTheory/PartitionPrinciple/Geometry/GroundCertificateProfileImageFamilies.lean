import OAI.SetTheory.PartitionPrinciple.Definability.PreparedCertificateCodes
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundMainFinalSupportedCertificateFamilies
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundCountableFunctionEnumerations

namespace OAI

namespace PartitionPilot.Forcing

namespace TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def synchronizedEnumerationBound (nodes N : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.prod (M.groundRelations ZFSet.omega nodes) (M.groundRelations ZFSet.omega N)

theorem synchronizedEnumerationBound_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {nodes N : ZFSet.{u}} (hNodes : nodes ∈ M.sets) (hN : N ∈ M.sets)
    (omega : ZFSet.omega ∈ M.sets) : M.synchronizedEnumerationBound nodes N ∈ M.sets :=
  M.prod_mem pairing unions powers separation
    (M.groundRelations_mem pairing unions powers separation omega hNodes)
    (M.groundRelations_mem pairing unions powers separation omega hN)

noncomputable def certificateEnumerationRelation (J nodes N k : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ j ∈ J, ∃ e ∈ M.groundRelations ZFSet.omega nodes,
    ∃ names ∈ M.groundRelations ZFSet.omega N,
      z = ZFSet.pair j (ZFSet.pair e names) ∧
      ∃ F B f, ZFSet.pair j (ZFSet.pair F (ZFSet.pair B f)) ∈ k ∧
        SynchronizedEnumerationCode ZFSet.omega N B f e names)
    (ZFSet.prod J (M.synchronizedEnumerationBound nodes N))

theorem pair_mem_certificateEnumerationRelation (J nodes N k j e names : ZFSet.{u}) :
    ZFSet.pair j (ZFSet.pair e names) ∈ M.certificateEnumerationRelation J nodes N k ↔
      j ∈ J ∧ e ∈ M.groundRelations ZFSet.omega nodes ∧
      names ∈ M.groundRelations ZFSet.omega N ∧
      ∃ F B f, ZFSet.pair j (ZFSet.pair F (ZFSet.pair B f)) ∈ k ∧
        SynchronizedEnumerationCode ZFSet.omega N B f e names := by
  rw [certificateEnumerationRelation, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, j', hj, e', he, names', hn, eq, F, B, f, stored, code⟩
    obtain ⟨rfl, tail⟩ := ZFSet.pair_inj.1 eq
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 tail
    exact ⟨hj, he, hn, F, B, f, stored, code⟩
  · rintro ⟨hj, he, hn, F, B, f, stored, code⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hj, ZFSet.pair_mem_prod.2 ⟨he, hn⟩⟩,
      j, hj, e, he, names, hn, rfl, F, B, f, stored, code⟩

theorem certificateEnumerationRelation_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {J nodes N k : ZFSet.{u}} (hJ : J ∈ M.sets) (hNodes : nodes ∈ M.sets)
    (hN : N ∈ M.sets) (hk : k ∈ M.sets) (omega : ZFSet.omega ∈ M.sets) :
    M.certificateEnumerationRelation J nodes N k ∈ M.sets := by
  have hE := M.groundRelations_mem pairing unions powers separation omega hNodes
  have hNames := M.groundRelations_mem pairing unions powers separation omega hN
  let params := extend J (extend (M.groundRelations ZFSet.omega nodes)
    (extend (M.groundRelations ZFSet.omega N) (extend ZFSet.omega
      (extend N (extend k Fin.elim0)))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.certificateEnumerationEntryFormula 0 1 2 3 4 5 6) params
    (Fin.cases hJ (Fin.cases hE (Fin.cases hNames (Fin.cases omega
      (Fin.cases hN (Fin.cases hk (fun i => Fin.elim0 i)))))))
    (M.prod_mem pairing unions powers separation hJ
      (M.synchronizedEnumerationBound_mem pairing unions powers separation hNodes hN omega))
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.certificateEnumerationEntryFormula 0 1 2 3 4 5 6)
      (extend z params)) (ZFSet.prod J (M.synchronizedEnumerationBound nodes N)) =
      M.certificateEnumerationRelation J nodes N k := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, certificateEnumerationRelation, ZFSet.mem_sep]
    exact and_congr Iff.rfl
      (BoundedFormula.truth_certificateEnumerationEntryFormula 0 1 2 3 4 5 6 _)
  exact equal ▸ selected

theorem exists_supportedCertificateEnumerations
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {J nodes N k : ZFSet.{u}} (hJ : J ∈ M.sets) (hNodes : nodes ∈ M.sets)
    (hN : N ∈ M.sets) (hk : k ∈ M.sets)
    (function : ZFSet.IsFunc J (M.supportedEqualityCertificateBound nodes N) k)
    (certificates : ∀ j F B f, ZFSet.pair j (ZFSet.pair F (ZFSet.pair B f)) ∈ k →
      B.Nonempty ∧ ZFSet.IsFunc B N f) :
    ∃ enumerations ∈ M.sets,
      ZFSet.IsFunc J (M.synchronizedEnumerationBound nodes N) enumerations ∧
      enumerations ⊆ M.certificateEnumerationRelation J nodes N k ∧
      ∀ j F B f e names, ZFSet.pair j (ZFSet.pair F (ZFSet.pair B f)) ∈ k →
        ZFSet.pair j (ZFSet.pair e names) ∈ enumerations →
        SynchronizedEnumerationCode ZFSet.omega N B f e names := by
  have omega := M.omega_mem separation infinite
  have bound := M.synchronizedEnumerationBound_mem pairing unions powers separation hNodes hN omega
  have relation := M.certificateEnumerationRelation_mem pairing unions powers separation
    hJ hNodes hN hk omega
  have total : ∀ j ∈ J, ∃ pair ∈ M.synchronizedEnumerationBound nodes N,
      ZFSet.pair j pair ∈ M.certificateEnumerationRelation J nodes N k := by
    intro j hj
    obtain ⟨c, jc, _⟩ := function.2 j hj
    have hc := (ZFSet.pair_mem_prod.1 (function.1 jc)).2
    obtain ⟨F, _, tail, htail, rfl⟩ := ZFSet.mem_prod.1 hc
    obtain ⟨B, _, f, _, rfl⟩ := ZFSet.mem_prod.1 htail
    have fields := (M.mem_supportedEqualityCertificateBound nodes N F B f).1
      (ZFSet.pair_mem_prod.1 (function.1 jc)).2
    obtain ⟨nonempty, ff⟩ := certificates j F B f jc
    obtain ⟨e, he, names, hn, ef, nf, onto, forward, backward⟩ :=
      M.groundFunction_enumeration pairing unions powers separation infinite
        fields.2.1.1 hN fields.2.2.1 nonempty fields.2.1.2.2 ff
    have eBound : e ∈ M.groundRelations ZFSet.omega nodes := by
      refine (M.mem_groundRelations ZFSet.omega nodes e).2 ⟨he, ?_⟩
      intro z hz
      obtain ⟨n, hno, v, hv, rfl⟩ := ZFSet.mem_prod.1 (ef.1 hz)
      exact ZFSet.pair_mem_prod.2 ⟨hno, fields.2.1.2.1 hv⟩
    have nBound := (M.mem_groundRelations ZFSet.omega N names).2 ⟨hn, nf.1⟩
    refine ⟨ZFSet.pair e names, ZFSet.pair_mem_prod.2 ⟨eBound, nBound⟩, ?_⟩
    exact (M.pair_mem_certificateEnumerationRelation J nodes N k j e names).2
      ⟨hj, eBound, nBound, F, B, f, jc, ff, ef, nf, onto, forward, backward⟩
  obtain ⟨enumerations, ground, selectedFunction, selected⟩ :=
    M.uniformize_relation pairing unions powers separation choice hJ bound relation total
  refine ⟨enumerations, ground, selectedFunction, selected, ?_⟩
  intro j F B f e names stored entry
  obtain ⟨hj, _, _, F', B', f', stored', code⟩ :=
    (M.pair_mem_certificateEnumerationRelation J nodes N k j e names).1 (selected entry)
  obtain ⟨_, _, unique⟩ := function.2 j hj
  have equal := (unique _ stored').trans (unique _ stored).symm
  have tail := (ZFSet.pair_inj.1 equal).2
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 tail
  exact code

end TransitiveGround

section
open SetFormula
universe u

def PreparedCertificateFamilyCode (M : TransitiveGround.{u})
    (P order q nodes nodeOrder meet N visibility top omega J C E k enumerations : ZFSet.{u}) : Prop :=
  ZFSet.IsFunc J C k ∧ ZFSet.IsFunc J E enumerations ∧
  ∀ z F B f e names, ZFSet.pair z (ZFSet.pair F (ZFSet.pair B f)) ∈ k →
    ZFSet.pair z (ZFSet.pair e names) ∈ enumerations →
    PreparedCertificateCode M P order q nodes nodeOrder meet N visibility top omega z F B f e names

namespace SetFormula

private def preparedFamilyEntries {n}
    (P order q nodes nodeOrder meet N visibility top omega k enumerations : Fin n) : SetFormula n :=
  .all (.all (.all (.all (.all (.all
    (imp (.conj (BoundedFormula.certificateGraphEntryAt 5 4 3 2
        k.succ.succ.succ.succ.succ.succ).toFormula
      (BoundedFormula.enumerationGraphEntryAt 5 1 0
        enumerations.succ.succ.succ.succ.succ.succ).toFormula)
      (preparedCertificateFormula P.succ.succ.succ.succ.succ.succ
        order.succ.succ.succ.succ.succ.succ q.succ.succ.succ.succ.succ.succ
        nodes.succ.succ.succ.succ.succ.succ nodeOrder.succ.succ.succ.succ.succ.succ
        meet.succ.succ.succ.succ.succ.succ N.succ.succ.succ.succ.succ.succ
        visibility.succ.succ.succ.succ.succ.succ top.succ.succ.succ.succ.succ.succ
        omega.succ.succ.succ.succ.succ.succ 5 4 3 2 1 0)))))))

def preparedCertificateFamilyFormula {n}
    (P order q nodes nodeOrder meet N visibility top omega J C E k enumerations : Fin n) : SetFormula n :=
  .conj (BoundedFormula.functionFormula J C k).toFormula
    (.conj (BoundedFormula.functionFormula J E enumerations).toFormula
      (preparedFamilyEntries P order q nodes nodeOrder meet N visibility top omega k enumerations))

end SetFormula
namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_preparedCertificateFamilyFormula {n}
    (P order q nodes nodeOrder meet N visibility top omega J C E k enumerations : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets)
    (meetCode : MeetOrderCode (env nodes) (env nodeOrder) (env meet)) :
    Realize M.sets
      (preparedCertificateFamilyFormula P order q nodes nodeOrder meet N visibility top omega J C E k enumerations) env ↔
      PreparedCertificateFamilyCode M (env P) (env order) (env q) (env nodes) (env nodeOrder)
        (env meet) (env N) (env visibility) (env top) (env omega) (env J)
        (env C) (env E) (env k) (env enumerations) := by
  have entries : Realize M.sets
      (SetFormula.preparedFamilyEntries P order q nodes nodeOrder meet N visibility top omega k enumerations) env ↔
      ∀ z F B f e names, ZFSet.pair z (ZFSet.pair F (ZFSet.pair B f)) ∈ env k →
        ZFSet.pair z (ZFSet.pair e names) ∈ env enumerations →
        PreparedCertificateCode M (env P) (env order) (env q) (env nodes) (env nodeOrder)
          (env meet) (env N) (env visibility) (env top) (env omega) z F B f e names := by
    let body := SetFormula.imp
      (.conj (BoundedFormula.certificateGraphEntryAt 5 4 3 2 k.succ.succ.succ.succ.succ.succ).toFormula
        (BoundedFormula.enumerationGraphEntryAt 5 1 0 enumerations.succ.succ.succ.succ.succ.succ).toFormula)
      (preparedCertificateFormula P.succ.succ.succ.succ.succ.succ order.succ.succ.succ.succ.succ.succ
        q.succ.succ.succ.succ.succ.succ nodes.succ.succ.succ.succ.succ.succ
        nodeOrder.succ.succ.succ.succ.succ.succ meet.succ.succ.succ.succ.succ.succ
        N.succ.succ.succ.succ.succ.succ visibility.succ.succ.succ.succ.succ.succ
        top.succ.succ.succ.succ.succ.succ omega.succ.succ.succ.succ.succ.succ 5 4 3 2 1 0)
    have meaning (z F B f e names : ZFSet.{u})
        (hz : z ∈ M.sets) (hF : F ∈ M.sets) (hB : B ∈ M.sets)
        (hf : f ∈ M.sets) (he : e ∈ M.sets) (hn : names ∈ M.sets) :
        Realize M.sets body (extend names (extend e (extend f (extend B (extend F (extend z env)))))) ↔
        (ZFSet.pair z (ZFSet.pair F (ZFSet.pair B f)) ∈ env k ∧
          ZFSet.pair z (ZFSet.pair e names) ∈ env enumerations →
          PreparedCertificateCode M (env P) (env order) (env q) (env nodes) (env nodeOrder)
            (env meet) (env N) (env visibility) (env top) (env omega) z F B f e names) := by
      have extended : ∀ i, (extend names (extend e (extend f (extend B (extend F (extend z env)))))) i ∈ M.sets := Fin.cases hn (Fin.cases he (Fin.cases hf
        (Fin.cases hB (Fin.cases hF (Fin.cases hz members)))))
      dsimp only [body]
      rw [realize_imp, Realize, BoundedFormula.realize_toFormula M _ _ extended,
        BoundedFormula.truth_certificateGraphEntryAt, BoundedFormula.realize_toFormula M _ _ extended,
        BoundedFormula.truth_enumerationGraphEntryAt,
        M.realize_preparedCertificateFormula
          P.succ.succ.succ.succ.succ.succ order.succ.succ.succ.succ.succ.succ
          q.succ.succ.succ.succ.succ.succ nodes.succ.succ.succ.succ.succ.succ
          nodeOrder.succ.succ.succ.succ.succ.succ meet.succ.succ.succ.succ.succ.succ
          N.succ.succ.succ.succ.succ.succ visibility.succ.succ.succ.succ.succ.succ
          top.succ.succ.succ.succ.succ.succ omega.succ.succ.succ.succ.succ.succ
          5 4 3 2 1 0 _ extended meetCode]
      rfl
    change (∀ z ∈ M.sets, ∀ F ∈ M.sets, ∀ B ∈ M.sets, ∀ f ∈ M.sets,
      ∀ e ∈ M.sets, ∀ names ∈ M.sets,
      Realize M.sets body (extend names (extend e (extend f (extend B (extend F (extend z env))))))) ↔ _
    constructor
    · intro holds z F B f e names stored enumerated
      have kc := M.pair_right (M.transitive (members k) stored)
      have ec := M.pair_right (M.transitive (members enumerations) enumerated)
      have hz := M.pair_left (M.transitive (members k) stored)
      have hF := M.pair_left kc
      have hB := M.pair_left (M.pair_right kc)
      have hf := M.pair_right (M.pair_right kc)
      have he := M.pair_left ec
      have hn := M.pair_right ec
      exact (meaning z F B f e names hz hF hB hf he hn).1
        (holds z hz F hF B hB f hf e he names hn) ⟨stored, enumerated⟩
    · intro holds z hz F hF B hB f hf e he names hn
      exact (meaning z F B f e names hz hF hB hf he hn).2
        (fun h => holds z F B f e names h.1 h.2)
  simp only [preparedCertificateFamilyFormula, Realize]
  rw [BoundedFormula.realize_toFormula M _ env members, BoundedFormula.truth_functionFormula,
    BoundedFormula.realize_toFormula M _ env members, BoundedFormula.truth_functionFormula, entries]
  rfl

end TransitiveGround

end

namespace TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def certificateProfileGraph (J nodes W k : ZFSet.{u}) : ZFSet.{u} :=
  relationCompose J (M.supportedEqualityCertificateBound nodes W) (M.groundPower nodes) k
    (productFirst (M.groundPower nodes)
      (ZFSet.prod (M.groundSmallSubsets nodes ZFSet.omega) (M.groundRelations nodes W)))

noncomputable def certificateProfileImage (J nodes W k : ZFSet.{u}) : ZFSet.{u} :=
  relationImage J (M.groundPower nodes) (M.certificateProfileGraph J nodes W k)

theorem certificateProfileGraph_function {J nodes W k : ZFSet.{u}}
    (function : ZFSet.IsFunc J (M.supportedEqualityCertificateBound nodes W) k) :
    ZFSet.IsFunc J (M.groundPower nodes) (M.certificateProfileGraph J nodes W k) :=
  relationCompose_function_of_subset function
    (productFirst_function (M.groundPower nodes)
      (ZFSet.prod (M.groundSmallSubsets nodes ZFSet.omega) (M.groundRelations nodes W)))
    (fun _ member => member)

theorem pair_mem_certificateProfileGraph {J nodes W k : ZFSet.{u}}
    (function : ZFSet.IsFunc J (M.supportedEqualityCertificateBound nodes W) k)
    (z F : ZFSet.{u}) :
    ZFSet.pair z F ∈ M.certificateProfileGraph J nodes W k ↔
      ∃ B f, ZFSet.pair z (ZFSet.pair F (ZFSet.pair B f)) ∈ k := by
  rw [certificateProfileGraph, pair_mem_relationCompose]
  constructor
  · rintro ⟨_, _, value, _, edge, projection⟩
    obtain ⟨profile, hp, tail, ht, equal⟩ := (mem_productFirst _ _ _).1 projection
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨B, hB, f, hf, rfl⟩ := ZFSet.mem_prod.1 ht
    exact ⟨B, f, edge⟩
  · rintro ⟨B, f, edge⟩
    have bounds := ZFSet.pair_mem_prod.1 (function.1 edge)
    have fields := ZFSet.pair_mem_prod.1 bounds.2
    exact ⟨bounds.1, fields.1, _, bounds.2, edge,
      (mem_productFirst _ _ _).2 ⟨F, fields.1, _, fields.2, rfl⟩⟩

theorem mem_certificateProfileImage {J nodes W k : ZFSet.{u}}
    (function : ZFSet.IsFunc J (M.supportedEqualityCertificateBound nodes W) k)
    (F : ZFSet.{u}) :
    F ∈ M.certificateProfileImage J nodes W k ↔
      ∃ z B f, ZFSet.pair z (ZFSet.pair F (ZFSet.pair B f)) ∈ k := by
  rw [certificateProfileImage, mem_relationImage]
  constructor
  · rintro ⟨_, z, _, edge⟩
    obtain ⟨B, f, selected⟩ := (M.pair_mem_certificateProfileGraph function z F).1 edge
    exact ⟨z, B, f, selected⟩
  · rintro ⟨z, B, f, edge⟩
    have projected := (M.pair_mem_certificateProfileGraph function z F).2 ⟨B, f, edge⟩
    have bounds := ZFSet.pair_mem_prod.1 ((M.certificateProfileGraph_function function).1 projected)
    exact ⟨bounds.2, z, bounds.1, projected⟩

theorem certificateProfileGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {J nodes W k : ZFSet.{u}} (hJ : J ∈ M.sets) (hNodes : nodes ∈ M.sets)
    (hW : W ∈ M.sets) (hk : k ∈ M.sets) (omega : ZFSet.omega ∈ M.sets) :
    M.certificateProfileGraph J nodes W k ∈ M.sets := by
  have hProfiles := M.groundPower_mem powers hNodes
  have hTail := M.prod_mem pairing unions powers separation
    (M.groundSmallSubsets_mem powers separation hNodes omega)
    (M.groundRelations_mem pairing unions powers separation hNodes hW)
  exact M.relationCompose_mem pairing unions powers separation hJ
    (M.supportedEqualityCertificateBound_mem pairing unions powers separation hNodes hW omega)
    hProfiles hk (M.productFirst_mem pairing unions powers separation hProfiles hTail)

theorem certificateProfileImage_mem_small
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {J nodes W k : ZFSet.{u}} (hJ : J ∈ M.sets) (hNodes : nodes ∈ M.sets)
    (hW : W ∈ M.sets) (hk : k ∈ M.sets) (omega : ZFSet.omega ∈ M.sets)
    (function : ZFSet.IsFunc J (M.supportedEqualityCertificateBound nodes W) k)
    (smallJ : M.groundEmbeddable J ZFSet.omega) :
    M.certificateProfileImage J nodes W k ∈ M.sets ∧
      M.groundEmbeddable (M.certificateProfileImage J nodes W k) ZFSet.omega := by
  have graph := M.certificateProfileGraph_mem pairing unions powers separation hJ hNodes hW hk omega
  have profiles := M.groundPower_mem powers hNodes
  exact ⟨M.relationImage_mem separation hJ profiles graph,
    M.groundEmbeddable_function_image pairing unions powers separation choice hJ profiles omega
      graph (M.certificateProfileGraph_function function) smallJ⟩

theorem certificateProfileImage_meetFilter
    {P order q nodes nodeOrder meet N visibility top omega J W k enumerations : ZFSet.{u}}
    (family : PreparedCertificateFamilyCode M P order q nodes nodeOrder meet N visibility top omega J
      (M.supportedEqualityCertificateBound nodes W) (M.synchronizedEnumerationBound nodes W)
      k enumerations) {F : ZFSet.{u}}
    (member : F ∈ M.certificateProfileImage J nodes W k) :
    MeetFilterCode nodes nodeOrder meet F := by
  obtain ⟨z, B, f, edge⟩ := (M.mem_certificateProfileImage family.1 F).1 member
  have hz := (ZFSet.pair_mem_prod.1 (family.1.1 edge)).1
  obtain ⟨value, enumerated, _unique⟩ := family.2.1.2 z hz
  have bounds := (ZFSet.pair_mem_prod.1 (family.2.1.1 enumerated)).2
  obtain ⟨e, _he, names, _hn, rfl⟩ := ZFSet.mem_prod.1 bounds
  exact (family.2.2 z F B f e names edge enumerated).1

theorem certificateProfileImage_eq_of_domain_subset {J D nodes W k : ZFSet.{u}}
    (function : ZFSet.IsFunc J (M.supportedEqualityCertificateBound nodes W) k)
    (subset : J ⊆ D) :
    M.certificateProfileImage D nodes W k = M.certificateProfileImage J nodes W k := by
  apply ZFSet.ext
  intro F
  simp only [certificateProfileImage, certificateProfileGraph, mem_relationImage,
    pair_mem_relationCompose]
  constructor
  · rintro ⟨hF, z, _hzD, _, _, c, hc, edge, projected⟩
    have hz := (ZFSet.pair_mem_prod.1 (function.1 edge)).1
    exact ⟨hF, z, hz, hz, hF, c, hc, edge, projected⟩
  · rintro ⟨hF, z, hz, _, _, c, hc, edge, projected⟩
    exact ⟨hF, z, subset hz, subset hz, hF, c, hc, edge, projected⟩

noncomputable def certificateProfileImageFamily (nodes W : ZFSet.{u}) : ZFSet.{u} :=
  familyCodeGraph
    (fun k : M.groundRelations W (M.supportedEqualityCertificateBound nodes W) => k.val)
    (fun k => M.certificateProfileImage W nodes W k.val)

theorem mem_certificateProfileImageFamily (nodes W z : ZFSet.{u}) :
    z ∈ M.certificateProfileImageFamily nodes W ↔
      ∃ k ∈ M.groundRelations W (M.supportedEqualityCertificateBound nodes W),
        z = ZFSet.pair k (M.certificateProfileImage W nodes W k) := by
  rw [certificateProfileImageFamily, mem_familyCodeGraph]
  constructor
  · rintro ⟨k, equal⟩
    exact ⟨k.val, k.property, equal.symm⟩
  · rintro ⟨k, hk, equal⟩
    exact ⟨⟨k, hk⟩, equal.symm⟩

theorem pair_mem_certificateProfileImageFamily (nodes W k image : ZFSet.{u}) :
    ZFSet.pair k image ∈ M.certificateProfileImageFamily nodes W ↔
      k ∈ M.groundRelations W (M.supportedEqualityCertificateBound nodes W) ∧
        image = M.certificateProfileImage W nodes W k := by
  rw [M.mem_certificateProfileImageFamily]
  constructor
  · rintro ⟨r, hr, equal⟩
    obtain ⟨rfl, value⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hr, value⟩
  · rintro ⟨hk, rfl⟩
    exact ⟨k, hk, rfl⟩

private noncomputable def profileRelationImageDefinition
    (separation : SeparationSchema M.sets) :
    GroundDefinableFunction M (fun env : Fin 3 → ZFSet.{u} =>
      relationImage (env 0) (env 1) (env 2)) where
  formula := (BoundedFormula.relationImageEqualityFormula 0 1 2 3).toFormula
  closed := fun _ members => M.relationImage_mem separation (members 0) (members 1) (members 2)
  correct := by
    intro env members z hz
    rw [BoundedFormula.realize_toFormula M _ _ (Fin.cases hz members),
      BoundedFormula.truth_relationImageEqualityFormula]
    rfl

private noncomputable def profileImageDefinition
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets) :
    GroundDefinableFunction M (fun env : Fin 5 → ZFSet.{u} =>
      relationImage (env 1) (env 3)
        (relationCompose (env 1) (env 2) (env 3) (env 0) (env 4))) := by
  let v := GroundSetTerm.var M (n := 5)
  let composed := GroundSetTerm.app (M.definable_relationCompose pairing unions powers separation)
    ![v 1, v 2, v 3, v 0, v 4]
  exact (GroundSetTerm.app (profileRelationImageDefinition M separation)
    ![v 1, v 3, composed]).definition

theorem certificateProfileImageFamily_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    {nodes W : ZFSet.{u}} (hNodes : nodes ∈ M.sets) (hW : W ∈ M.sets)
    (omega : ZFSet.omega ∈ M.sets) :
    M.certificateProfileImageFamily nodes W ∈ M.sets := by
  let C := M.supportedEqualityCertificateBound nodes W
  let PF := M.groundPower nodes
  let projection := productFirst PF
    (ZFSet.prod (M.groundSmallSubsets nodes ZFSet.omega) (M.groundRelations nodes W))
  have hC := M.supportedEqualityCertificateBound_mem pairing unions powers separation hNodes hW omega
  have hPF := M.groundPower_mem powers hNodes
  have hProjection := M.productFirst_mem pairing unions powers separation hPF
    (M.prod_mem pairing unions powers separation
      (M.groundSmallSubsets_mem powers separation hNodes omega)
      (M.groundRelations_mem pairing unions powers separation hNodes hW))
  let defined := profileImageDefinition M pairing unions powers separation
  change defined.graph (extend W (extend C (extend PF (extend projection Fin.elim0))))
    (M.groundRelations W C) ∈ M.sets
  exact defined.graph_mem pairing separation collection _
    (Fin.cases hW (Fin.cases hC (Fin.cases hPF (Fin.cases hProjection (fun j => Fin.elim0 j)))))
    (M.groundRelations_mem pairing unions powers separation hW hC)

theorem certificateProfileImageFamily_function
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {nodes W : ZFSet.{u}} (hNodes : nodes ∈ M.sets) (hW : W ∈ M.sets)
    (omega : ZFSet.omega ∈ M.sets) :
    ZFSet.IsFunc (M.groundRelations W (M.supportedEqualityCertificateBound nodes W))
      (M.groundPower (M.groundPower nodes)) (M.certificateProfileImageFamily nodes W) := by
  refine ⟨?_, ?_⟩
  · intro z hz
    obtain ⟨k, hk, rfl⟩ := (M.mem_certificateProfileImageFamily nodes W z).1 hz
    have groundK := ((M.mem_groundRelations _ _ k).1 hk).1
    have groundGraph := M.certificateProfileGraph_mem pairing unions powers separation
      hW hNodes hW groundK omega
    have groundImage := M.relationImage_mem separation hW (M.groundPower_mem powers hNodes)
      groundGraph
    exact ZFSet.pair_mem_prod.2 ⟨hk, (M.mem_groundPower _ _).2
      ⟨groundImage, fun F member => (mem_relationImage _ _ _ F).1 member |>.1⟩⟩
  · intro k hk
    exact ⟨M.certificateProfileImage W nodes W k,
      (M.pair_mem_certificateProfileImageFamily nodes W k _).2 ⟨hk, rfl⟩,
      fun image edge => ((M.pair_mem_certificateProfileImageFamily nodes W k image).1 edge).2⟩

end TransitiveGround

end PartitionPilot.Forcing

end OAI
