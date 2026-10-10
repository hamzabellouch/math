import Mathlib
import OAI.Topology.ArtinGroups.Realizations.CellUnion
import OAI.Topology.ArtinGroups.Realizations.ModelFaceHomeomorph

namespace OAI

namespace HarmonicArtin
open Topology Set CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type*} [Fintype S] [DecidableEq S] (M : CoxeterMatrix S)

lemma weightMax_orderIso {P Q : Type*} [PartialOrder P] [PartialOrder Q]
    (e : P ≃o Q) (w : OrderWeights P) :
    weightMax (weightMap (e : P →o Q) w)=e (weightMax w) := by
  apply le_antisymm
  · have hm := weightMax_mem (weightMap (e : P →o Q) w)
    rw [weightMap_support_embedding _ e.injective] at hm
    obtain ⟨p,hp,hpe⟩ := Finset.mem_image.mp hm
    rw [←hpe]
    exact e.monotone (le_weightMax w p hp)
  · apply le_weightMax
    rw [weightMap_support_embedding _ e.injective]
    exact Finset.mem_image.mpr ⟨weightMax w,weightMax_mem w,rfl⟩

omit [Fintype S] [DecidableEq S] in
lemma liftedWeights_max_smul (g : Artin M) (w : OrderWeights (LiftedCell M)) :
    weightMax (g • w)=liftedDeck M g (weightMax w) :=
  weightMax_orderIso (liftedDeck M g) w

noncomputable def sourceCharacteristic (T : SphericalType M) :
    C(SourceModelCell M T,SourceSalvetti M) where
  toFun x := Quotient.mk _ ⟨T,x⟩
  continuous_toFun := continuous_quotient_mk'.comp continuous_sigmaMk

lemma sourceCharacteristic_deck (a : LiftedCell M) (x : SourceModelCell M a.2) :
    sourceSalvettiHomeomorph M (sourceCharacteristic M a.2 x)=
      salvettiDeckProjection M (sourceCellMap M a x) := sourceUnionMap_lifted M a x

lemma sourceCharacteristic_incidence {a b : LiftedCell M} (h : a ≤ b)
    (x : SourceModelCell M a.2) :
    sourceCharacteristic M b.2 (sourceModelFaceMap M h x)=sourceCharacteristic M a.2 x := by
  apply (sourceSalvettiHomeomorph M).injective
  rw [sourceCharacteristic_deck M b,sourceCharacteristic_deck M a,sourceModelFaceMap_included]

abbrev SourceModelInterior (T : SphericalType M) :=
  {x : SourceModelCell M T // x.val ∈ interior (permutahedron (restrictedMatrix M T.val))}

noncomputable def sourceOpenCell (T : SphericalType M) : Set (SourceSalvetti M) :=
  Set.range (fun x : SourceModelInterior M T => sourceCharacteristic M T x.val)

lemma sourceCharacteristic_interior_unique
    {T R : SphericalType M} (x : SourceModelCell M T) (y : SourceModelCell M R)
    (hx : x.val ∈ interior (permutahedron (restrictedMatrix M T.val)))
    (hy : y.val ∈ interior (permutahedron (restrictedMatrix M R.val)))
    (he : sourceCharacteristic M T x=sourceCharacteristic M R y) :
    (⟨T,x⟩ : SourceCellUnion M)=⟨R,y⟩ := by
  have hd := congrArg (sourceSalvettiHomeomorph M) he
  rw [sourceCharacteristic_deck M (1,T),sourceCharacteristic_deck M (1,R)] at hd
  obtain ⟨g,hg⟩ := (salvettiDeckProjection_quotientCovering M).apply_eq_iff_mem_orbit.mp hd
  have hm := congrArg weightMax hg
  rw [liftedWeights_max_smul,(sourceCellMap_interior_iff M (1,R) y).mp hy,
    (sourceCellMap_interior_iff M (1,T) x).mp hx] at hm
  have hge : g=1 := by
    have h := congrArg (fun c : LiftedCell M => c.1) hm
    change g*1=1 at h
    simpa only [mul_one] using h
  have hRT : R=T := congrArg (fun c : LiftedCell M => c.2) hm
  subst R
  subst g
  change (1 : Artin M) • sourceCellMap M (1,T) y=sourceCellMap M (1,T) x at hg
  rw [one_smul] at hg
  have hxy := sourceCellMap_injective M (1,T) hg
  subst y
  rfl

lemma sourceCharacteristic_interior_injective (T : SphericalType M) :
    Function.Injective (fun x : SourceModelInterior M T => sourceCharacteristic M T x.val) := by
  intro x y h
  have he := sourceCharacteristic_interior_unique M x.val y.val x.property y.property h
  have hv : x.val=y.val := eq_of_heq (Sigma.mk.inj he).2
  exact Subtype.ext hv

lemma sourceOpenCell_disjoint {T R : SphericalType M} (h : T≠R) :
    Disjoint (sourceOpenCell M T) (sourceOpenCell M R) := by
  apply Set.disjoint_left.mpr
  rintro q ⟨x,hx⟩ ⟨y,hy⟩
  have he := sourceCharacteristic_interior_unique M x.val y.val x.property y.property (hx.trans hy.symm)
  exact h (congrArg Sigma.fst he)

lemma sourceOpenCell_cover (q : SourceSalvetti M) : ∃ T,q ∈ sourceOpenCell M T := by
  obtain ⟨w,hw⟩ := (sourceUniversalProjection_quotientCovering M).surjective q
  let a := weightMax w
  obtain ⟨x,hx⟩ := sourceCellMap_range M a w (le_weightMax w)
  have hi : x.val ∈ interior (permutahedron (restrictedMatrix M a.2.val)) :=
    (sourceCellMap_interior_iff M a x).mpr (by rw [hx])
  refine ⟨a.2,⟨⟨x,hi⟩,?_⟩⟩
  apply (sourceSalvettiHomeomorph M).injective
  rw [sourceCharacteristic_deck M a,hx,←hw]
  exact ((sourceSalvettiHomeomorph M).apply_symm_apply _).symm

lemma sourceCharacteristic_boundary_lower (T : SphericalType M) (x : SourceModelCell M T)
    (hx : x.val ∈ frontier (permutahedron (restrictedMatrix M T.val))) :
    ∃ R : SphericalType M,R.val.ncard<T.val.ncard ∧
      sourceCharacteristic M T x ∈ Set.range (sourceCharacteristic M R) := by
  let w := sourceCellMap M (1,T) x
  let a := weightMax w
  have ha : a < ((1,T) : LiftedCell M) :=
    lt_of_le_of_ne (sourceCellMap_support M (1,T) x a (weightMax_mem w))
      ((sourceCellMap_frontier_iff M (1,T) x).mp hx)
  obtain ⟨y,hy⟩ := sourceCellMap_range M a w (le_weightMax w)
  refine ⟨a.2,lifted_rank_strict M ha,⟨y,?_⟩⟩
  apply (sourceSalvettiHomeomorph M).injective
  rw [sourceCharacteristic_deck M a,sourceCharacteristic_deck M (1,T),hy]

lemma sourceCharacteristic_weak (A : Set (SourceSalvetti M)) :
    IsClosed A ↔ ∀ T,IsClosed ((sourceCharacteristic M T) ⁻¹' A) := by
  have hq : IsQuotientMap (fun x : SourceCellUnion M => (Quotient.mk _ x : SourceSalvetti M)) :=
    isQuotientMap_quotient_mk'
  exact hq.1.isClosed_preimage.symm.trans isClosed_sigma_iff

end HarmonicArtin

end OAI
