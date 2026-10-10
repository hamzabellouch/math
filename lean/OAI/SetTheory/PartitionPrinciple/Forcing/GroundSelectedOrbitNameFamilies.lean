import OAI.SetTheory.PartitionPrinciple.Geometry.GroundDefinableIndexBounds

namespace OAI

open scoped ZFSet



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)

private noncomputable def orbitTopPairsDefinition
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets) :
    GroundDefinableFunction M (fun env : Fin 2 → ZFSet.{u} => ZFSet.prod (env 0) {env 1}) := by
  let v := GroundSetTerm.var M (n := 2)
  let singleton := GroundSetTerm.app (M.definable_singleton pairing) ![v 1]
  exact (GroundSetTerm.app (M.definable_product pairing unions powers separation) ![v 0, singleton]).definition

theorem exists_groundOrbitNameCodeFamily
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
    (maps : a.conditionMapFamily s t ∈ M.sets)
    (one J : ZFSet.{u}) (hOne : one ∈ M.sets) (hJ : J ∈ M.sets) :
    ∃ family ∈ M.sets, FunctionGraphOn J family ∧
      ∀ sigma z, ZFSet.pair sigma z ∈ family ↔
        sigma ∈ J ∧ z = ZFSet.prod (a.orbitCodes s (M.nameDomain s) {sigma}) {one} := by
  let singleton := (M.definable_singleton pairing).graph Fin.elim0 J
  have singletonFunction : FunctionGraphOn J singleton :=
    (M.definable_singleton pairing).graph_function Fin.elim0 J
  have singletonGround : singleton ∈ M.sets :=
    (M.definable_singleton pairing).graph_mem pairing separation collection Fin.elim0 (fun j => Fin.elim0 j) hJ
  let S := functionGraphRange J singleton
  have hS : S ∈ M.sets := M.functionGraphRange_mem unions separation hJ singletonGround
  let orbits := M.orbitCodeFamily a s S
  have orbitFunction : FunctionGraphOn S orbits := M.orbitCodeFamily_function a s S
  have orbitGround : orbits ∈ M.sets :=
    M.orbitCodeFamily_mem a s t pairing unions powers separation collection carrier group maps hS
  let O := functionGraphRange S orbits
  have hO : O ∈ M.sets := M.functionGraphRange_mem unions separation hS orbitGround
  let topPairs := (orbitTopPairsDefinition M pairing unions powers separation).graph (extend one Fin.elim0) O
  have topFunction : FunctionGraphOn O topPairs :=
    (orbitTopPairsDefinition M pairing unions powers separation).graph_function _ O
  have topGround : topPairs ∈ M.sets :=
    (orbitTopPairsDefinition M pairing unions powers separation).graph_mem pairing separation collection
      (extend one Fin.elim0) (Fin.cases hOne (fun j => Fin.elim0 j)) hO
  let V := functionGraphRange O topPairs
  have hV : V ∈ M.sets := M.functionGraphRange_mem unions separation hO topGround
  let first := relationCompose J S O singleton orbits
  have firstFunction : ZFSet.IsFunc J O first := relationCompose_function_of_subset
    (functionGraphRange_function singletonFunction) (functionGraphRange_function orbitFunction) (fun _ h => h)
  have firstGround : first ∈ M.sets := M.relationCompose_mem pairing unions powers separation
    hJ hS hO singletonGround orbitGround
  let family := relationCompose J O V first topPairs
  have function : FunctionGraphOn J family := ⟨V, relationCompose_function_of_subset
    firstFunction (functionGraphRange_function topFunction) (fun _ h => h)⟩
  have ground : family ∈ M.sets := M.relationCompose_mem pairing unions powers separation
    hJ hO hV firstGround topGround
  have values (sigma z : ZFSet.{u}) (entry : ZFSet.pair sigma z ∈ family) :
      sigma ∈ J ∧ z = ZFSet.prod (a.orbitCodes s (M.nameDomain s) {sigma}) {one} := by
    obtain ⟨inJ, _, orbit, _, firstEntry, topEntry⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 entry
    obtain ⟨_, _, input, _, singletonEntry, orbitEntry⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 firstEntry
    have inputValue := ((M.definable_singleton pairing).pair_mem_graph Fin.elim0 J sigma input).1 singletonEntry |>.2
    have topValue := ((orbitTopPairsDefinition M pairing unions powers separation).pair_mem_graph
      (extend one Fin.elim0) O orbit z).1 topEntry |>.2
    obtain ⟨W, _, pairEqual⟩ := (M.mem_orbitCodeFamily a s S (ZFSet.pair input orbit)).1 orbitEntry
    obtain ⟨rfl, orbitValue⟩ := ZFSet.pair_inj.1 pairEqual
    change input = {sigma} at inputValue
    change z = ZFSet.prod orbit {one} at topValue
    exact ⟨inJ, topValue.trans (congrArg (fun X => ZFSet.prod X {one})
      (orbitValue.trans (congrArg (a.orbitCodes s (M.nameDomain s)) inputValue)))⟩
  refine ⟨family, ground, function, ?_⟩
  intro sigma z
  refine ⟨values sigma z, ?_⟩
  rintro ⟨inJ, equal⟩
  obtain ⟨w, entry⟩ := function.total inJ
  exact ((values sigma w entry).2.trans equal.symm) ▸ entry

end TransitiveGround
end PartitionPilot.Forcing




namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)

private noncomputable def selectedImageDefinition (separation : SeparationSchema M.sets) :
    GroundDefinableFunction M (fun env : Fin 3 → ZFSet.{u} => relationImage (env 0) (env 1) (env 2)) where
  formula := (BoundedFormula.relationImageEqualityFormula 0 1 2 3).toFormula
  closed := fun _ members => M.relationImage_mem separation (members 0) (members 1) (members 2)
  correct := by
    intro env members z hz
    rw [BoundedFormula.realize_toFormula M _ _ (Fin.cases hz members),
      BoundedFormula.truth_relationImageEqualityFormula]
    rfl

private noncomputable def jointCodeDefinition
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0) :
    GroundDefinableFunction M (fun env : Fin 3 → ZFSet.{u} => orderedPairNameCode (env 0) (env 1) (env 2)) where
  formula := orderedPairNameCodeFormula 0 2 3 1
  closed := fun _ members => M.orderedPairNameCode_mem pairing (members 0) (members 1) (members 2)
  correct := fun _ members _ hz => M.realize_orderedPairNameCodeFormula pairing 0 2 3 1 _ (Fin.cases hz members)

private noncomputable def selectedJointDefinition
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0) (separation : SeparationSchema M.sets) :
    GroundDefinableFunction M (fun env : Fin 4 → ZFSet.{u} =>
      orderedPairNameCode (env 1) (⋃₀ relationImage {env 0} (env 2) (env 3)) (env 0)) := by
  let v := GroundSetTerm.var M (n := 4)
  let input := GroundSetTerm.app (M.definable_singleton pairing) ![v 0]
  let image := GroundSetTerm.app (selectedImageDefinition M separation) ![input, v 2, v 3]
  let selected := GroundSetTerm.app (M.definable_sUnion unions) ![image]
  exact (GroundSetTerm.app (jointCodeDefinition M pairing) ![v 1, selected, v 0]).definition

private theorem selectedImage_value {W T choice tau tuple : ZFSet.{u}}
    (function : ZFSet.IsFunc W T choice) (entry : ZFSet.pair tau tuple ∈ choice) :
    ⋃₀ relationImage {tau} T choice = tuple := by
  have single : relationImage {tau} T choice = {tuple} := by
    apply ZFSet.ext
    intro z
    rw [mem_relationImage, ZFSet.mem_singleton]
    constructor
    · rintro ⟨_, x, hx, edge⟩
      have same := ZFSet.mem_singleton.1 hx
      subst x
      exact (show FunctionGraphOn W choice from ⟨T, function⟩).unique edge entry
    · rintro rfl
      exact ⟨(ZFSet.pair_mem_prod.1 (function.1 entry)).2,
        tau, ZFSet.mem_singleton.2 rfl, entry⟩
  rw [single]
  apply ZFSet.ext
  intro z
  rw [ZFSet.mem_sUnion]
  constructor
  · rintro ⟨X, hX, member⟩
    exact (ZFSet.mem_singleton.1 hX) ▸ member
  · intro member
    exact ⟨tuple, ZFSet.mem_singleton.2 rfl, member⟩

theorem exists_groundSelectedOrbitNameFamily
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
    (maps : a.conditionMapFamily s t ∈ M.sets)
    (one W T choice : ZFSet.{u}) (hOne : one ∈ M.sets) (hW : W ∈ M.sets)
    (hT : T ∈ M.sets) (hChoice : choice ∈ M.sets) (function : ZFSet.IsFunc W T choice) :
    ∃ family ∈ M.sets, FunctionGraphOn W family ∧
      ∀ tau tuple, ZFSet.pair tau tuple ∈ choice → ∀ z,
        ZFSet.pair tau z ∈ family ↔
          z = ZFSet.prod (a.orbitCodes s (M.nameDomain s) {orderedPairNameCode one tuple tau}) {one} := by
  let params := extend one (extend T (extend choice Fin.elim0))
  let joints := (selectedJointDefinition M pairing unions separation).graph params W
  have jointGround : joints ∈ M.sets :=
    (selectedJointDefinition M pairing unions separation).graph_mem pairing separation collection params
      (Fin.cases hOne (Fin.cases hT (Fin.cases hChoice (fun j => Fin.elim0 j)))) hW
  have jointFunction : FunctionGraphOn W joints :=
    (selectedJointDefinition M pairing unions separation).graph_function params W
  let J := functionGraphRange W joints
  have hJ : J ∈ M.sets := M.functionGraphRange_mem unions separation hW jointGround
  obtain ⟨orbits, hOrbits, orbitFunction, orbitValues⟩ := M.exists_groundOrbitNameCodeFamily
    a s t pairing unions powers separation collection carrier group maps one J hOne hJ
  let O := functionGraphRange J orbits
  have hO : O ∈ M.sets := M.functionGraphRange_mem unions separation hJ hOrbits
  let family := relationCompose W J O joints orbits
  have familyGround : family ∈ M.sets := M.relationCompose_mem pairing unions powers separation
    hW hJ hO jointGround hOrbits
  have familyFunction : FunctionGraphOn W family := ⟨O, relationCompose_function_of_subset
    (functionGraphRange_function jointFunction) (functionGraphRange_function orbitFunction) (fun _ h => h)⟩
  have values (tau tuple : ZFSet.{u}) (selected : ZFSet.pair tau tuple ∈ choice)
      (z : ZFSet.{u}) (entry : ZFSet.pair tau z ∈ family) :
      z = ZFSet.prod (a.orbitCodes s (M.nameDomain s) {orderedPairNameCode one tuple tau}) {one} := by
    obtain ⟨_, _, joint, _, jointEntry, orbitEntry⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 entry
    have jointValue := ((selectedJointDefinition M pairing unions separation).pair_mem_graph params W tau joint).1 jointEntry |>.2
    change joint = orderedPairNameCode one (⋃₀ relationImage {tau} T choice) tau at jointValue
    rw [selectedImage_value function selected] at jointValue
    exact ((orbitValues joint z).1 orbitEntry).2.trans
      (congrArg (fun x => ZFSet.prod (a.orbitCodes s (M.nameDomain s) {x}) {one}) jointValue)
  refine ⟨family, familyGround, familyFunction, ?_⟩
  intro tau tuple selected z
  refine ⟨values tau tuple selected z, ?_⟩
  intro equal
  obtain ⟨w, entry⟩ := familyFunction.total (ZFSet.pair_mem_prod.1 (function.1 selected)).1
  exact ((values tau tuple selected w entry).trans equal.symm) ▸ entry

end TransitiveGround
end PartitionPilot.Forcing

end OAI
