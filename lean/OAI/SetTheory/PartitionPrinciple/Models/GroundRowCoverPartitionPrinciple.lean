import OAI.SetTheory.PartitionPrinciple.Definability.RefinementValidityCodes
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundIndexedClassInclusions
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundPartialCoverPartitions
import OAI.SetTheory.PartitionPrinciple.Models.GroundOrdinalPartitionInjectionAssembly

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (N : TransitiveGround.{u})

theorem function_kernel_quotient
    (zf : ZFRealization N.sets) {U V f : ZFSet.{u}}
    (hU : U ∈ N.sets) (hV : V ∈ N.sets) (hf : f ∈ N.sets)
    (function : ZFSet.IsFunc U V f)
    (onto : ∀ x ∈ V, ∃ u ∈ U, ZFSet.pair u x ∈ f) :
    ∃ R ∈ N.sets, EquivalenceRelationCode U R ∧
      (∀ u v, ZFSet.pair u v ∈ R ↔ u ∈ U ∧ v ∈ U ∧
        ∃ x ∈ V, ZFSet.pair u x ∈ f ∧ ZFSet.pair v x ∈ f) ∧
      ∃ a ∈ N.sets, InjectionCode (equivalenceClasses U R) V a ∧
        (∀ x ∈ V, ∃ C ∈ equivalenceClasses U R, ZFSet.pair C x ∈ a) ∧
        (∀ u x, ZFSet.pair u x ∈ f →
          ZFSet.pair (equivalenceClass U R u) x ∈ a) := by
  have pairing : Realize N.sets SetFormula.pairing Fin.elim0 := zf.1.2.2.2.1
  have unions : Realize N.sets SetFormula.union Fin.elim0 := zf.1.2.2.2.2.1
  have powers : Realize N.sets powerSet Fin.elim0 := zf.1.2.2.2.2.2.1
  let inverse := relationConverse U V f
  let R := relationCompose U V U f inverse
  have inverseGround := N.relationConverse_mem pairing unions powers zf.2.1 hU hV hf
  have hR : R ∈ N.sets :=
    N.relationCompose_mem pairing unions powers zf.2.1 hU hV hU hf inverseGround
  have entries (u v : ZFSet.{u}) : ZFSet.pair u v ∈ R ↔ u ∈ U ∧ v ∈ U ∧
      ∃ x ∈ V, ZFSet.pair u x ∈ f ∧ ZFSet.pair v x ∈ f := by
    simp only [R, inverse, pair_mem_relationCompose, pair_mem_relationConverse]
    exact ⟨fun ⟨hu, hv, x, hx, ux, _, _, vx⟩ => ⟨hu, hv, x, hx, ux, vx⟩,
      fun ⟨hu, hv, x, hx, ux, vx⟩ => ⟨hu, hv, x, hx, ux, hv, hx, vx⟩⟩
  have unique {u x y : ZFSet.{u}} (ux : ZFSet.pair u x ∈ f)
      (uy : ZFSet.pair u y ∈ f) : x = y := by
    obtain ⟨v, _, unique⟩ := function.2 u (ZFSet.pair_mem_prod.1 (function.1 ux)).1
    exact (unique x ux).trans (unique y uy).symm
  have equivalence : EquivalenceRelationCode U R := by
    refine ⟨fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_, ?_, ?_⟩
    · intro u hu
      obtain ⟨x, ux, _⟩ := function.2 u hu
      exact (entries u u).2 ⟨hu, hu, x, (ZFSet.pair_mem_prod.1 (function.1 ux)).2, ux, ux⟩
    · intro u v uv
      obtain ⟨hu, hv, x, hx, ux, vx⟩ := (entries u v).1 uv
      exact (entries v u).2 ⟨hv, hu, x, hx, vx, ux⟩
    · intro u v w uv vw
      obtain ⟨hu, _, x, hx, ux, vx⟩ := (entries u v).1 uv
      obtain ⟨_, hw, y, _, vy, wy⟩ := (entries v w).1 vw
      exact (entries u w).2 ⟨hu, hw, x, hx, ux, (unique vy vx) ▸ wy⟩
  let Q := equivalenceClasses U R
  let classifier := equivalenceClassifier U R
  let backward := relationConverse U Q classifier
  let a := relationCompose Q U V backward f
  have hQ : Q ∈ N.sets := N.equivalenceClasses_mem powers zf.2.1 hU hR
  have hClassifier : classifier ∈ N.sets :=
    N.equivalenceClassifier_mem pairing unions powers zf.2.1 hU hR
  have hBackward : backward ∈ N.sets :=
    N.relationConverse_mem pairing unions powers zf.2.1 hU hQ hClassifier
  have ha : a ∈ N.sets := N.relationCompose_mem pairing unions powers zf.2.1 hQ hU hV hBackward hf
  have aEntries (C x : ZFSet.{u}) : ZFSet.pair C x ∈ a ↔
      C ∈ Q ∧ x ∈ V ∧ ∃ u ∈ U, C = equivalenceClass U R u ∧ ZFSet.pair u x ∈ f := by
    change ZFSet.pair C x ∈ relationCompose Q U V backward f ↔ _
    rw [pair_mem_relationCompose]
    constructor
    · rintro ⟨hC, hx, u, hu, cu, ux⟩
      have uc := (pair_mem_relationConverse U Q classifier u C).1 cu
      have equal := (pair_mem_equivalenceClassifier U R u C).1 uc.2.2
      exact ⟨hC, hx, u, hu, equal.2, ux⟩
    · rintro ⟨hC, hx, u, hu, equal, ux⟩
      exact ⟨hC, hx, u, hu, (pair_mem_relationConverse U Q classifier u C).2
        ⟨hu, hC, (pair_mem_equivalenceClassifier U R u C).2 ⟨hu, equal⟩⟩, ux⟩
  have canonical (u x : ZFSet.{u}) (ux : ZFSet.pair u x ∈ f) :
      ZFSet.pair (equivalenceClass U R u) x ∈ a := by
    obtain ⟨hu, hx⟩ := ZFSet.pair_mem_prod.1 (function.1 ux)
    exact (aEntries _ x).2 ⟨Forcing.equivalenceClass_mem hu, hx, u, hu, rfl, ux⟩
  have injection : InjectionCode Q V a := by
    refine ⟨⟨fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_⟩, ?_⟩
    · intro C hC
      obtain ⟨u, hu, rfl⟩ := (mem_equivalenceClasses U R C).1 hC
      obtain ⟨x, ux, _⟩ := function.2 u hu
      refine ⟨x, canonical u x ux, ?_⟩
      intro y cy
      obtain ⟨_, _, v, hv, equal, vy⟩ := (aEntries _ y).1 cy
      obtain ⟨_, _, z, _, uz, vz⟩ := (entries u v).1 ((equivalence.class_eq_iff hu hv).1 equal)
      exact (unique vy vz).trans (unique uz ux)
    · intro C D x cx dx
      obtain ⟨_, hx, u, hu, rfl, ux⟩ := (aEntries C x).1 cx
      obtain ⟨_, _, v, hv, rfl, vx⟩ := (aEntries D x).1 dx
      exact (equivalence.class_eq_iff hu hv).2 ((entries u v).2 ⟨hu, hv, x, hx, ux, vx⟩)
  refine ⟨R, hR, equivalence, entries, a, ha, injection, ?_, canonical⟩
  intro x hx
  obtain ⟨u, hu, ux⟩ := onto x hx
  exact ⟨equivalenceClass U R u, Forcing.equivalenceClass_mem hu, canonical u x ux⟩

theorem partialCover_quotient_injection
    (zf : ZFRealization N.sets) {T B X Y X' Y' h f : ZFSet.{u}}
    (quotientInjection : ∀ U ∈ N.sets, ∀ Rf ∈ N.sets, ∀ Rc ∈ N.sets,
      RefinementValidityCode T U Rf Rc →
        N.groundEmbeddable (equivalenceClasses U Rc) (equivalenceClasses U Rf))
    (hT : T ∈ N.sets) (_hX : X ∈ N.sets) (_hY : Y ∈ N.sets)
    (hX' : X' ∈ N.sets) (hY' : Y' ∈ N.sets) (hh : h ∈ N.sets) (hf : f ∈ N.sets)
    (partialCode : PartialFunctionCode T B h) (function : ZFSet.IsFunc X Y f)
    (sourceSubset : X' ⊆ X) (_targetSubset : Y' ⊆ Y)
    (maps : ∀ x ∈ X', ∀ y, ZFSet.pair x y ∈ f → y ∈ Y')
    (onto : ∀ y ∈ Y', ∃ x ∈ X', ZFSet.pair x y ∈ f)
    (covered : ∀ x ∈ X', ∃ u ∈ T, ZFSet.pair u x ∈ h) :
    N.groundEmbeddable Y' X' := by
  have pairing : Realize N.sets SetFormula.pairing Fin.elim0 := zf.1.2.2.2.1
  have unions : Realize N.sets SetFormula.union Fin.elim0 := zf.1.2.2.2.2.1
  have powers : Realize N.sets powerSet Fin.elim0 := zf.1.2.2.2.2.2.1
  let inverse := relationConverse T X' h
  let U := relationImage X' T inverse
  have hInverse : inverse ∈ N.sets :=
    N.relationConverse_mem pairing unions powers zf.2.1 hT hX' hh
  have hU : U ∈ N.sets := N.relationImage_mem zf.2.1 hX' hT hInverse
  have uEntries (u : ZFSet.{u}) : u ∈ U ↔ u ∈ T ∧ ∃ x ∈ X', ZFSet.pair u x ∈ h := by
    simp only [U, inverse, mem_relationImage, pair_mem_relationConverse]
    exact ⟨fun ⟨hu, x, hx, _, _, ux⟩ => ⟨hu, x, hx, ux⟩,
      fun ⟨hu, x, hx, ux⟩ => ⟨hu, x, hx, hu, hx, ux⟩⟩
  let h' := ZFSet.sep (fun z => z ∈ ZFSet.prod U X') h
  have hh' : h' ∈ N.sets := N.injection_restriction_mem zf.2.1 hU hX' hh
  have hEntries (u x : ZFSet.{u}) : ZFSet.pair u x ∈ h' ↔
      ZFSet.pair u x ∈ h ∧ u ∈ U ∧ x ∈ X' := by
    exact ZFSet.mem_sep.trans (and_congr_right fun _ => ZFSet.pair_mem_prod)
  have hFunction : ZFSet.IsFunc U X' h' := by
    refine ⟨fun _ hz => (ZFSet.mem_sep.1 hz).2, ?_⟩
    intro u hu
    obtain ⟨_, x, hx, ux⟩ := (uEntries u).1 hu
    exact ⟨x, (hEntries u x).2 ⟨ux, hu, hx⟩,
      fun y uy => partialCode.unique u y x ((hEntries u y).1 uy).1 ux⟩
  have hOnto : ∀ x ∈ X', ∃ u ∈ U, ZFSet.pair u x ∈ h' := by
    intro x hx
    obtain ⟨u, hu, ux⟩ := covered x hx
    have member := (uEntries u).2 ⟨hu, x, hx, ux⟩
    exact ⟨u, member, (hEntries u x).2 ⟨ux, member, hx⟩⟩
  let f' := ZFSet.sep (fun z => z ∈ ZFSet.prod X' Y') f
  have hf' : f' ∈ N.sets := N.injection_restriction_mem zf.2.1 hX' hY' hf
  have fEntries (x y : ZFSet.{u}) : ZFSet.pair x y ∈ f' ↔
      ZFSet.pair x y ∈ f ∧ x ∈ X' ∧ y ∈ Y' := by
    exact ZFSet.mem_sep.trans (and_congr_right fun _ => ZFSet.pair_mem_prod)
  have fFunction : ZFSet.IsFunc X' Y' f' := by
    refine ⟨fun _ hz => (ZFSet.mem_sep.1 hz).2, ?_⟩
    intro x hx
    obtain ⟨y, xy, unique⟩ := function.2 x (sourceSubset hx)
    exact ⟨y, (fEntries x y).2 ⟨xy, hx, maps x hx y xy⟩,
      fun z xz => unique z ((fEntries x z).1 xz).1⟩
  let g := relationCompose U X' Y' h' f'
  have hg : g ∈ N.sets := N.relationCompose_mem pairing unions powers zf.2.1 hU hX' hY' hh' hf'
  have gFunction : ZFSet.IsFunc U Y' g :=
    relationCompose_function_of_subset hFunction fFunction (fun _ hx => hx)
  have gOnto : ∀ y ∈ Y', ∃ u ∈ U, ZFSet.pair u y ∈ g := by
    intro y hy
    obtain ⟨x, hx, xy⟩ := onto y hy
    obtain ⟨u, hu, ux⟩ := hOnto x hx
    exact ⟨u, hu, (pair_mem_relationCompose U X' Y' h' f' u y).2
      ⟨hu, hy, x, hx, ux, (fEntries x y).2 ⟨xy, hx, hy⟩⟩⟩
  obtain ⟨Rf, hRf, fine, fineEntries, a, ha, aInjection, _aOnto, _aCanonical⟩ :=
    N.function_kernel_quotient zf hU hX' hh' hFunction hOnto
  obtain ⟨Rc, hRc, coarse, coarseEntries, b, hb, bInjection, bOnto, _bCanonical⟩ :=
    N.function_kernel_quotient zf hU hY' hg gFunction gOnto
  have refines : Rf ⊆ Rc := by
    intro z hz
    obtain ⟨u, hu, v, hv, rfl⟩ := ZFSet.mem_prod.1 (fine.shape hz)
    obtain ⟨_, _, x, hx, ux, vx⟩ := (fineEntries u v).1 hz
    obtain ⟨y, xy, _⟩ := fFunction.2 x hx
    have hy := (ZFSet.pair_mem_prod.1 (fFunction.1 xy)).2
    exact (coarseEntries u v).2 ⟨hu, hv, y, hy,
      (pair_mem_relationCompose U X' Y' h' f' u y).2 ⟨hu, hy, x, hx, ux, xy⟩,
      (pair_mem_relationCompose U X' Y' h' f' v y).2 ⟨hv, hy, x, hx, vx, xy⟩⟩
  obtain ⟨ell, hEll, ellInjection⟩ := quotientInjection U hU Rf hRf Rc hRc
    ⟨fun u hu => ((uEntries u).1 hu).1, fine, coarse, refines⟩
  have fineGround := N.equivalenceClasses_mem powers zf.2.1 hU hRf
  have coarseGround := N.equivalenceClasses_mem powers zf.2.1 hU hRc
  have imageEq : relationImage (equivalenceClasses U Rc) Y' b = Y' := by
    apply ZFSet.ext
    intro y
    rw [mem_relationImage]
    exact ⟨And.left, fun hy => ⟨hy, bOnto y hy⟩⟩
  have inverseInjection : InjectionCode Y' (equivalenceClasses U Rc)
      (relationConverse (equivalenceClasses U Rc) Y' b) := by
    have inverse := bInjection.converse_image
    rw [imageEq] at inverse
    exact inverse
  have inverseGround := N.relationConverse_mem pairing unions powers zf.2.1 coarseGround hY' hb
  let first := relationCompose Y' (equivalenceClasses U Rc) (equivalenceClasses U Rf)
    (relationConverse (equivalenceClasses U Rc) Y' b) ell
  have firstGround : first ∈ N.sets := N.relationCompose_mem pairing unions powers zf.2.1
    hY' coarseGround fineGround inverseGround hEll
  exact ⟨relationCompose Y' (equivalenceClasses U Rf) X' first a,
    N.relationCompose_mem pairing unions powers zf.2.1 hY' fineGround hX' firstGround ha,
    (inverseInjection.compose ellInjection).compose aInjection⟩

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (N : TransitiveGround.{u})

theorem partitionPrinciple_of_rowCover_quotients
    (zf : ZFRealization N.sets) {T : ZFSet.{u}} (hT : T ∈ N.sets)
    (acwo : ∀ delta ∈ N.sets, ordinalSetProperty delta →
      ∀ z ∈ N.sets, FunctionGraphOn delta z →
        (∀ beta A, ZFSet.pair beta A ∈ z → A.Nonempty) →
        ∃ c ∈ N.sets, FunctionGraphOn delta c ∧
          ∀ beta A x, ZFSet.pair beta A ∈ z → ZFSet.pair beta x ∈ c → x ∈ A)
    (rowCover : ∀ X ∈ N.sets, ∃ delta ∈ N.sets, ordinalSetProperty delta ∧
      ∃ h ∈ N.sets, FunctionGraphOn delta h ∧
        (∀ i hi, ZFSet.pair i hi ∈ h → PartialFunctionCode T (⋃₀ ⋃₀ hi) hi) ∧
        ∀ x ∈ X, ∃ i ∈ delta, ∃ hi, ZFSet.pair i hi ∈ h ∧
          ∃ u ∈ T, ZFSet.pair u x ∈ hi)
    (quotientInjection : ∀ U ∈ N.sets, ∀ Rf ∈ N.sets, ∀ Rc ∈ N.sets,
      RefinementValidityCode T U Rf Rc →
        N.groundEmbeddable (equivalenceClasses U Rc) (equivalenceClasses U Rf)) :
    ∀ X ∈ N.sets, ∀ Y ∈ N.sets, ∀ f ∈ N.sets, ZFSet.IsFunc X Y f →
      (∀ y ∈ Y, ∃ x ∈ X, ZFSet.pair x y ∈ f) → N.groundEmbeddable Y X := by
  intro X hX Y hY f hf function onto
  obtain ⟨delta, hDelta, ordinal, h, hh, family, partials, cover⟩ := rowCover X hX
  obtain ⟨full, _hFull, p, hp, q, hq, fullFunction, pFunction, qFunction,
      bounds, coverY, disjointY, disjointX, pieces⟩ :=
    N.partialCover_ordinal_partitions zf hDelta ordinal hT hX hY hh hf family function onto cover
  apply N.ordinalPartition_injection_assembly zf acwo hDelta ordinal hY hX hp hq
    pFunction qFunction bounds coverY disjointY disjointX
  intro i hi U V ip iq
  obtain ⟨g, ig⟩ := family.total hi
  obtain ⟨A, iA⟩ := fullFunction.total hi
  obtain ⟨_original, _least, _source, _hRestrict, restrictFunction, restrictOnto, covered⟩ :=
    pieces i g A U V ig iA ip iq
  have hU : U ∈ N.sets := N.pair_right (N.transitive hp ip)
  have hV : V ∈ N.sets := N.pair_right (N.transitive hq iq)
  have hg : g ∈ N.sets := N.pair_right (N.transitive hh ig)
  apply N.partialCover_quotient_injection zf quotientInjection hT hX hY hV hU hg hf
    (partials i g ig) function (bounds i U V ip iq).2 (bounds i U V ip iq).1
  · intro x hx y xy
    exact (ZFSet.pair_mem_prod.1 (restrictFunction.1
      (pair_mem_graphRestriction.2 ⟨xy, hx⟩))).2
  · intro y hy
    obtain ⟨x, hx, xy⟩ := restrictOnto y hy
    exact ⟨x, hx, (pair_mem_graphRestriction.1 xy).1⟩
  · exact covered

end PartitionPilot.Forcing.TransitiveGround

end OAI
