import OAI.SetTheory.PartitionPrinciple.Definability.GroundRefinementPairClassGraphs

namespace OAI

open scoped ZFSet

section

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

noncomputable def indexedGraphNameCode (one I f : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (fun a : {a : ↥I × ↥(⋃₀ ⋃₀ f) // ZFSet.pair a.1.val a.2.val ∈ f} =>
    ZFSet.pair (orderedPairNameCode one (checkNameCode one a.val.1.val) a.val.2.val) one)

theorem mem_indexedGraphNameCode (one I f z : ZFSet.{u}) :
    z ∈ indexedGraphNameCode one I f ↔ ∃ i ∈ I, ∃ v,
      ZFSet.pair i v ∈ f ∧ z = ZFSet.pair (orderedPairNameCode one (checkNameCode one i) v) one := by
  rw [indexedGraphNameCode, ZFSet.mem_range]
  constructor
  · rintro ⟨a, equal⟩
    exact ⟨a.val.1.val, a.val.1.property, a.val.2.val, a.property, equal.symm⟩
  · rintro ⟨i, hi, v, entry, equal⟩
    exact ⟨⟨(⟨i, hi⟩, ⟨v, pair_second_mem_doubleUnion entry⟩), entry⟩, equal.symm⟩

theorem indexedGraphNameCode_eq {P : Type u} (s : Presentation P) (one : P)
    {I f : ZFSet.{u}} (function : FunctionGraphOn I f)
    (names : ∀ i, IsName s (function.value i)) :
    indexedGraphNameCode (s.encode one) I f = (Name.indexedGraphName one function names).val := by
  apply ZFSet.ext
  intro z
  rw [mem_indexedGraphNameCode, Name.mem_indexedGraphName_code]
  constructor
  · rintro ⟨i, hi, v, entry, equal⟩
    let j : I.toSet := ⟨i, hi⟩
    have value := function.value_eq_of_entry j entry
    refine ⟨j, ?_⟩
    rw [Name.check_code_eq, value]
    exact equal
  · rintro ⟨i, equal⟩
    refine ⟨i.val, i.property, function.value i, function.value_entry i, ?_⟩
    rwa [Name.check_code_eq] at equal

namespace SetFormula

def indexedGraphNamePairFormula : SetFormula 4 :=
  ex (ex (ex (ex (.conj (.mem 3 6)
    (.conj (orderedPairFormula 4 3 2)
      (.conj (checkNameCodeFormula 1 3 7)
        (.conj (orderedPairNameCodeFormula 0 1 2 7)
          (orderedPairFormula 5 0 7))))))))

def indexedGraphNameCodeFormula : SetFormula 4 :=
  exactSetFormula 0 (reindex (extend 0 (extend 4 (extend 3 (extend 2 Fin.elim0))))
    (relationImageFormula indexedGraphNamePairFormula))

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0)
variable (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
include pairing unions powers separation collection

theorem realize_indexedGraphNamePairFormula {one I r z : ZFSet.{u}}
    (hone : one ∈ M.sets) (hI : I ∈ M.sets) (hr : r ∈ M.sets) (hz : z ∈ M.sets) :
    Realize M.sets indexedGraphNamePairFormula (extend r (extend z (extend I (extend one Fin.elim0)))) ↔
      ∃ i ∈ I, ∃ v, r = ZFSet.pair i v ∧
        z = ZFSet.pair (orderedPairNameCode one (checkNameCode one i) v) one := by
  rw [indexedGraphNamePairFormula, realize_ex]
  constructor
  · rintro ⟨i, hiM, rest⟩
    obtain ⟨v, hv, rest⟩ := (realize_ex M.sets _ _).1 rest
    obtain ⟨k, hk, rest⟩ := (realize_ex M.sets _ _).1 rest
    obtain ⟨w, hw, hi, input, checked, named, output⟩ := (realize_ex M.sets _ _).1 rest
    have members : ∀ j, (extend w (extend k (extend v (extend i
        (extend r (extend z (extend I (extend one Fin.elim0)))))))) j ∈ M.sets :=
      Fin.cases hw (Fin.cases hk (Fin.cases hv (Fin.cases hiM (Fin.cases hr
        (Fin.cases hz (Fin.cases hI (Fin.cases hone (fun j => Fin.elim0 j))))))))
    have key := (M.realize_checkNameCodeFormula pairing unions powers separation collection 1 3 7 _ members).1 checked
    have name := (M.realize_orderedPairNameCodeFormula pairing 0 1 2 7 _ members).1 named
    have inp := (M.realize_orderedPairFormula pairing 4 3 2 _ hr hiM hv).1 input
    have out := (M.realize_orderedPairFormula pairing 5 0 7 _ hz hw hone).1 output
    refine ⟨i, hi, v, inp, ?_⟩
    exact out.trans (congrArg (fun a => ZFSet.pair a one)
      (name.trans (congrArg (fun a => orderedPairNameCode one a v) key)))
  · rintro ⟨i, hi, v, input, output⟩
    have hiM := M.transitive hI hi
    have hv := M.pair_right (input ▸ hr)
    have hk := M.checkNameCode_mem pairing unions powers separation collection hone hiM
    have hw := M.orderedPairNameCode_mem pairing hone hk hv
    refine ⟨i, hiM, ?_⟩
    rw [realize_ex]
    refine ⟨v, hv, ?_⟩
    rw [realize_ex]
    refine ⟨checkNameCode one i, hk, ?_⟩
    rw [realize_ex]
    have members : ∀ j, (extend (orderedPairNameCode one (checkNameCode one i) v)
      (extend (checkNameCode one i) (extend v (extend i
        (extend r (extend z (extend I (extend one Fin.elim0)))))))) j ∈ M.sets :=
      Fin.cases hw (Fin.cases hk (Fin.cases hv (Fin.cases hiM (Fin.cases hr
        (Fin.cases hz (Fin.cases hI (Fin.cases hone (fun j => Fin.elim0 j))))))))
    exact ⟨_, hw, hi, (M.realize_orderedPairFormula pairing 4 3 2 _ hr hiM hv).2 input,
      (M.realize_checkNameCodeFormula pairing unions powers separation collection 1 3 7 _ members).2 rfl,
      (M.realize_orderedPairNameCodeFormula pairing 0 1 2 7 _ members).2 rfl,
      (M.realize_orderedPairFormula pairing 5 0 7 _ hz hw hone).2 output⟩

theorem indexedGraphNameCode_mem {one I f : ZFSet.{u}}
    (hone : one ∈ M.sets) (hI : I ∈ M.sets) (hf : f ∈ M.sets) :
    indexedGraphNameCode one I f ∈ M.sets := by
  let params := extend I (extend one Fin.elim0)
  apply M.definable_image_mem separation collection indexedGraphNamePairFormula params
    (Fin.cases hI (Fin.cases hone (fun j => Fin.elim0 j))) hf
  · intro z hz
    obtain ⟨i, hi, v, entry, rfl⟩ := (mem_indexedGraphNameCode one I f z).1 hz
    exact M.orderedPair_mem pairing (M.orderedPairNameCode_mem pairing hone
      (M.checkNameCode_mem pairing unions powers separation collection hone (M.transitive hI hi))
      (M.pair_right (M.transitive hf entry))) hone
  · intro z hz
    rw [mem_indexedGraphNameCode]
    constructor
    · rintro ⟨i, hi, v, entry, equal⟩
      exact ⟨ZFSet.pair i v, entry,
        (M.realize_indexedGraphNamePairFormula pairing unions powers separation collection
          hone hI (M.transitive hf entry) hz).2 ⟨i, hi, v, rfl, equal⟩⟩
    · rintro ⟨r, hr, formula⟩
      obtain ⟨i, hi, v, shape, equal⟩ :=
        (M.realize_indexedGraphNamePairFormula pairing unions powers separation collection
          hone hI (M.transitive hf hr) hz).1 formula
      exact ⟨i, hi, v, shape ▸ hr, equal⟩
  · intro r hr y hy z hz first second
    obtain ⟨i, _, v, input, output⟩ :=
      (M.realize_indexedGraphNamePairFormula pairing unions powers separation collection
        hone hI (M.transitive hf hr) hy).1 first
    obtain ⟨j, _, w, input', output'⟩ :=
      (M.realize_indexedGraphNamePairFormula pairing unions powers separation collection
        hone hI (M.transitive hf hr) hz).1 second
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 (input.symm.trans input')
    exact output.trans output'.symm

theorem realize_indexedGraphNameCodeFormula {one I f z : ZFSet.{u}}
    (hone : one ∈ M.sets) (hI : I ∈ M.sets) (hf : f ∈ M.sets) (hz : z ∈ M.sets) :
    Realize M.sets indexedGraphNameCodeFormula (extend z (extend one (extend I (extend f Fin.elim0)))) ↔
      z = indexedGraphNameCode one I f := by
  apply M.realize_exactSetFormula 0 _ _ hz
    (fun _ member => M.transitive (M.indexedGraphNameCode_mem pairing unions powers separation collection hone hI hf) member)
  intro w hw
  rw [realize_reindex, map_extend, map_extend, map_extend, map_extend, map_empty]
  change Realize M.sets (relationImageFormula indexedGraphNamePairFormula)
    (extend w (extend f (extend I (extend one Fin.elim0)))) ↔ w ∈ indexedGraphNameCode one I f
  rw [M.realize_relationImageFormula indexedGraphNamePairFormula (extend I (extend one Fin.elim0)) f w hf,
    mem_indexedGraphNameCode]
  constructor
  · rintro ⟨r, hr, formula⟩
    obtain ⟨i, hi, v, shape, equal⟩ :=
      (M.realize_indexedGraphNamePairFormula pairing unions powers separation collection
        hone hI (M.transitive hf hr) hw).1 formula
    exact ⟨i, hi, v, shape ▸ hr, equal⟩
  · rintro ⟨i, hi, v, entry, equal⟩
    exact ⟨ZFSet.pair i v, entry,
      (M.realize_indexedGraphNamePairFormula pairing unions powers separation collection
        hone hI (M.transitive hf entry) hw).2 ⟨i, hi, v, rfl, equal⟩⟩

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

theorem indexedGraphNameCode_enlarge {one I J f : ZFSet.{u}}
    (function : FunctionGraphOn I f) (subset : I ⊆ J) :
    indexedGraphNameCode one J f = indexedGraphNameCode one I f := by
  apply ZFSet.ext
  intro z
  rw [mem_indexedGraphNameCode, mem_indexedGraphNameCode]
  constructor
  · rintro ⟨i, _, v, entry, equal⟩
    exact ⟨i, function.pair_source entry, v, entry, equal⟩
  · rintro ⟨i, hi, v, entry, equal⟩
    exact ⟨i, subset hi, v, entry, equal⟩

noncomputable def indexedGraphNameFamily (one I F : ZFSet.{u}) : ZFSet.{u} :=
  familyCodeGraph (fun f : F => f.val) (fun f => indexedGraphNameCode one I f.val)

theorem mem_indexedGraphNameFamily (one I F z : ZFSet.{u}) :
    z ∈ indexedGraphNameFamily one I F ↔
      ∃ f ∈ F, z = ZFSet.pair f (indexedGraphNameCode one I f) := by
  rw [indexedGraphNameFamily, mem_familyCodeGraph]
  constructor
  · rintro ⟨f, equal⟩
    exact ⟨f.val, f.property, equal.symm⟩
  · rintro ⟨f, hf, equal⟩
    exact ⟨⟨f, hf⟩, equal.symm⟩

theorem pair_mem_indexedGraphNameFamily (one I F f z : ZFSet.{u}) :
    ZFSet.pair f z ∈ indexedGraphNameFamily one I F ↔
      f ∈ F ∧ z = indexedGraphNameCode one I f := by
  rw [mem_indexedGraphNameFamily]
  constructor
  · rintro ⟨g, hg, equal⟩
    obtain ⟨rfl, equal⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hg, equal⟩
  · rintro ⟨hf, rfl⟩
    exact ⟨f, hf, rfl⟩

theorem indexedGraphNameFamily_function (one I F : ZFSet.{u}) :
    FunctionGraphOn F (indexedGraphNameFamily one I F) := by
  have eq : ZFSet.range (fun f : F => f.val) = F := by
    apply ZFSet.ext
    intro f
    rw [ZFSet.mem_range]
    constructor
    · rintro ⟨g, equal⟩
      exact equal ▸ g.property
    · intro hf
      exact ⟨⟨f, hf⟩, rfl⟩
  simpa only [indexedGraphNameFamily, eq] using familyCodeGraph_function (fun f : F => f.val)
    (fun f => indexedGraphNameCode one I f.val) Subtype.val_injective

namespace SetFormula

def indexedGraphNameFamilyPairFormula : SetFormula 4 :=
  .ex (.conj
    (reindex (extend 0 (extend 3 (extend 4 (extend 1 Fin.elim0)))) indexedGraphNameCodeFormula)
    (orderedPairFormula 2 1 0))

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0)
variable (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
include pairing unions powers separation collection

noncomputable def definable_indexedGraphNameCode : GroundDefinableFunction M
    (fun env : Fin 3 → ZFSet.{u} => indexedGraphNameCode (env 0) (env 1) (env 2)) where
  formula := indexedGraphNameCodeFormula
  closed := fun _ members => M.indexedGraphNameCode_mem pairing unions powers separation collection
    (members 0) (members 1) (members 2)
  correct := by
    intro env members z hz
    have equal : env = extend (env 0) (extend (env 1) (extend (env 2) Fin.elim0)) := by
      funext j
      refine Fin.cases rfl (fun j => ?_) j
      refine Fin.cases rfl (fun j => ?_) j
      exact Fin.cases rfl (fun i => Fin.elim0 i) j
    have result := M.realize_indexedGraphNameCodeFormula pairing unions powers separation collection
      (members 0) (members 1) (members 2) hz
    rw [← equal] at result
    exact result

theorem realize_indexedGraphNameFamilyPairFormula {one I f z : ZFSet.{u}}
    (hone : one ∈ M.sets) (hI : I ∈ M.sets) (hf : f ∈ M.sets) (hz : z ∈ M.sets) :
    Realize M.sets indexedGraphNameFamilyPairFormula
      (extend f (extend z (extend one (extend I Fin.elim0)))) ↔
      z = ZFSet.pair f (indexedGraphNameCode one I f) := by
  rw [indexedGraphNameFamilyPairFormula, realize_ex]
  constructor
  · rintro ⟨v, hv, code, pair⟩
    rw [realize_reindex, map_extend, map_extend, map_extend, map_extend, map_empty] at code
    have value := (M.realize_indexedGraphNameCodeFormula pairing unions powers separation collection
      hone hI hf hv).1 code
    have equal := (M.realize_orderedPairFormula pairing 2 1 0 _ hz hf hv).1 pair
    exact value ▸ equal
  · intro equal
    have hv := M.indexedGraphNameCode_mem pairing unions powers separation collection hone hI hf
    refine ⟨indexedGraphNameCode one I f, hv, ?_,
      (M.realize_orderedPairFormula pairing 2 1 0 _ hz hf hv).2 equal⟩
    rw [realize_reindex, map_extend, map_extend, map_extend, map_extend, map_empty]
    exact (M.realize_indexedGraphNameCodeFormula pairing unions powers separation collection
      hone hI hf hv).2 rfl

theorem indexedGraphNameFamily_mem {one I F : ZFSet.{u}}
    (hone : one ∈ M.sets) (hI : I ∈ M.sets) (hF : F ∈ M.sets) :
    indexedGraphNameFamily one I F ∈ M.sets := by
  apply M.definable_image_mem separation collection indexedGraphNameFamilyPairFormula
    (extend one (extend I Fin.elim0))
    (Fin.cases hone (Fin.cases hI (fun j => Fin.elim0 j))) hF
  · intro z hz
    obtain ⟨f, hf, rfl⟩ := (mem_indexedGraphNameFamily one I F z).1 hz
    exact M.orderedPair_mem pairing (M.transitive hF hf)
      (M.indexedGraphNameCode_mem pairing unions powers separation collection hone hI (M.transitive hF hf))
  · intro z hz
    rw [mem_indexedGraphNameFamily]
    exact exists_congr (fun f => and_congr_right (fun hf =>
      (M.realize_indexedGraphNameFamilyPairFormula pairing unions powers separation collection
        hone hI (M.transitive hF hf) hz).symm))
  · intro f hf y hy z hz first second
    exact ((M.realize_indexedGraphNameFamilyPairFormula pairing unions powers separation collection
      hone hI (M.transitive hF hf) hy).1 first).trans
      ((M.realize_indexedGraphNameFamilyPairFormula pairing unions powers separation collection
        hone hI (M.transitive hF hf) hz).1 second).symm

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
