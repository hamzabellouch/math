import Mathlib
import OAI.Topology.ArtinGroups.Realizations.WeightPrincipalProjection
import OAI.Topology.ArtinGroups.Harmonic.PrincipalOrderIso

namespace OAI

namespace HarmonicArtin
open Topology

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type*} [Fintype S] [DecidableEq S] (M : CoxeterMatrix S)

abbrev SourceCellUnion := Σ T : SphericalType M, SourceModelCell M T

inductive SourceFaceIdentification : SourceCellUnion M → SourceCellUnion M → Prop
  | face (T : SphericalType M) (a : LiftedCell M) (h : a < (1,T))
      (x : SourceModelCell M a.2) :
      SourceFaceIdentification ⟨a.2,x⟩ ⟨T,sourceModelFaceMap M h.le x⟩

abbrev SourceGluingRelation := Relation.EqvGen (SourceFaceIdentification M)

def SourceSalvetti := Quotient (Relation.EqvGen.setoid (SourceFaceIdentification M))

instance : TopologicalSpace (SourceSalvetti M) :=
  inferInstanceAs (TopologicalSpace (Quotient (Relation.EqvGen.setoid (SourceFaceIdentification M))))

noncomputable def sourceUnionMap : C(SourceCellUnion M,SalvettiDeckQuotient M) where
  toFun x := salvettiDeckProjection M (sourceCellMap M (1,x.1) x.2)
  continuous_toFun := continuous_sigma_iff.mpr (fun T =>
    (salvettiDeckProjection_quotientCovering M).continuous.comp (sourceCellMap M (1,T)).continuous)

lemma sourceCellMap_normal (a : LiftedCell M) (x : SourceModelCell M a.2) :
    sourceCellMap M a x=a.1 • sourceCellMap M (1,a.2) x := by
  have h := sourceCellMap_deck M a.1 (1,a.2) x
  change sourceCellMap M (a.1*1,a.2) x=a.1 • sourceCellMap M (1,a.2) x at h
  rw [_root_.mul_one] at h
  exact h

lemma sourceUnionMap_lifted (a : LiftedCell M) (x : SourceModelCell M a.2) :
    sourceUnionMap M ⟨a.2,x⟩=salvettiDeckProjection M (sourceCellMap M a x) := by
  rw [sourceCellMap_normal]
  exact ((salvettiDeckProjection_quotientCovering M).map_smul a.1).symm

lemma sourceGluing_face_le {T : SphericalType M} {a : LiftedCell M} (h : a ≤ (1,T))
    (x : SourceModelCell M a.2) :
    SourceGluingRelation M ⟨a.2,x⟩ ⟨T,sourceModelFaceMap M h x⟩ := by
  rcases h.eq_or_lt with he|hl
  · subst a
    rw [sourceModelFaceMap_self]
    exact Relation.EqvGen.refl _
  · exact Relation.EqvGen.rel _ _ (SourceFaceIdentification.face (M := M) T a hl x)

lemma sourceUnionMap_rel (x y : SourceCellUnion M) (h : SourceGluingRelation M x y) :
    sourceUnionMap M x=sourceUnionMap M y := by
  induction h with
  | rel x y h =>
    cases h with
    | face T a h z =>
      rw [sourceUnionMap_lifted M a z]
      change salvettiDeckProjection M (sourceCellMap M a z)=
        salvettiDeckProjection M (sourceCellMap M (1,T) (sourceModelFaceMap M h.le z))
      rw [sourceModelFaceMap_included]
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

lemma sourceUnionMap_kernel (x y : SourceCellUnion M)
    (h : sourceUnionMap M x=sourceUnionMap M y) : SourceGluingRelation M x y := by
  rcases x with ⟨T,x⟩
  rcases y with ⟨R,y⟩
  obtain ⟨g,hg⟩ := (salvettiDeckProjection_quotientCovering M).apply_eq_iff_mem_orbit.mp h
  let w := sourceCellMap M (1,R) y
  let b := weightMax w
  have hb : b ≤ ((1,R) : LiftedCell M) := sourceCellMap_support M (1,R) y b (weightMax_mem w)
  obtain ⟨z,hz⟩ := sourceCellMap_range M b w (le_weightMax w)
  have hy : sourceModelFaceMap M hb z=y := by
    apply sourceCellMap_injective M (1,R)
    exact (sourceModelFaceMap_included M hb z).trans hz
  let c : LiftedCell M := (g*b.1,b.2)
  have hw : c ∈ (sourceCellMap M (1,T) x).weights.support := by
    rw [←hg,Finsupp.mem_support_iff]
    change (g • w).weights (liftedDeck M g b) ≠ 0
    rw [liftedWeights_smul_apply]
    exact Finsupp.mem_support_iff.mp (weightMax_mem w)
  have hc : c ≤ ((1,T) : LiftedCell M) := sourceCellMap_support M (1,T) x c hw
  have hx : sourceModelFaceMap M hc z=x := by
    apply sourceCellMap_injective M (1,T)
    calc
      _ = sourceCellMap M c z := sourceModelFaceMap_included M hc z
      _ = g • sourceCellMap M b z := sourceCellMap_deck M g b z
      _ = g • w := congrArg (g • ·) hz
      _ = _ := hg
  have hR := sourceGluing_face_le M hb z
  have hT := sourceGluing_face_le M hc z
  rw [hy] at hR
  rw [hx] at hT
  exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hT) hR

lemma sourceUnionMap_surjective : Function.Surjective (sourceUnionMap M) := by
  intro q
  obtain ⟨w,rfl⟩ := (salvettiDeckProjection_quotientCovering M).surjective q
  obtain ⟨x,hx⟩ := sourceCellMap_range M (weightMax w) w (le_weightMax w)
  refine ⟨⟨(weightMax w).2,x⟩,?_⟩
  rw [sourceUnionMap_lifted,hx]

lemma sourceUnionMap_quotient : IsQuotientMap (sourceUnionMap M) := by
  rw [isQuotientMap_iff_isClosed]
  refine ⟨sourceUnionMap_surjective M,fun A => ⟨fun h => h.preimage (sourceUnionMap M).continuous,?_⟩⟩
  intro h
  apply (salvettiDeckProjection_quotientCovering M).toIsQuotientMap.1.isClosed_preimage.mp
  apply weightPrincipalProjection_quotient.1.isClosed_preimage.mp
  rw [isClosed_sigma_iff]
  intro a
  have hc := (isClosed_sigma_iff.mp h a.2).preimage (liftedModelHomeomorph M a).symm.continuous
  have he : ∀ z : OrderWeights (Set.Iic a),
      sourceUnionMap M ⟨a.2,(liftedModelHomeomorph M a).symm z⟩=
      salvettiDeckProjection M (weightMap (weightInclusion (Set.Iic a)) z) := by
    intro z
    rw [sourceUnionMap_lifted]
    change salvettiDeckProjection M (weightMap _ ((liftedModelHomeomorph M a)
      ((liftedModelHomeomorph M a).symm z)))=_
    rw [Homeomorph.apply_symm_apply]
  simpa only [Set.preimage_preimage,Function.comp_def,he,weightPrincipalProjection] using hc

noncomputable def sourceSalvettiToDeck : C(SourceSalvetti M,SalvettiDeckQuotient M) where
  toFun := Quotient.lift (sourceUnionMap M) (sourceUnionMap_rel M)
  continuous_toFun := (sourceUnionMap M).continuous.quotient_lift (sourceUnionMap_rel M)

lemma sourceSalvettiToDeck_bijective : Function.Bijective (sourceSalvettiToDeck M) := by
  constructor
  · intro x y h
    induction x using Quotient.inductionOn with
    | h x =>
      induction y using Quotient.inductionOn with
      | h y => exact Quotient.sound (sourceUnionMap_kernel M x y h)
  · intro y
    obtain ⟨x,hx⟩ := sourceUnionMap_surjective M y
    exact ⟨Quotient.mk _ x,hx⟩

lemma sourceSalvettiToDeck_quotient : IsQuotientMap (sourceSalvettiToDeck M) :=
  IsQuotientMap.of_comp continuous_quotient_mk' (sourceSalvettiToDeck M).continuous
    (sourceUnionMap_quotient M)

noncomputable def sourceSalvettiHomeomorph : SourceSalvetti M ≃ₜ SalvettiDeckQuotient M := by
  let e := Equiv.ofBijective (sourceSalvettiToDeck M) (sourceSalvettiToDeck_bijective M)
  refine { toEquiv := e,continuous_toFun := (sourceSalvettiToDeck M).continuous,continuous_invFun := ?_ }
  rw [(sourceSalvettiToDeck_quotient M).continuous_iff]
  have he : e.symm ∘ sourceSalvettiToDeck M=id := funext e.symm_apply_apply
  change Continuous (e.symm ∘ sourceSalvettiToDeck M)
  rw [he]
  exact continuous_id

noncomputable def sourceUniversalProjection : OrderWeights (LiftedCell M) → SourceSalvetti M :=
  (sourceSalvettiHomeomorph M).symm ∘ salvettiDeckProjection M

theorem sourceUniversalProjection_quotientCovering :
    IsQuotientCoveringMap (sourceUniversalProjection M) (Artin M) :=
  (salvettiDeckProjection_quotientCovering M).homeomorph_comp (sourceSalvettiHomeomorph M).symm

theorem source_full_cover_contractible :
    IsCoveringMap (sourceUniversalProjection M) ∧ ContractibleSpace (OrderWeights (LiftedCell M)) :=
  ⟨(sourceUniversalProjection_quotientCovering M).isCoveringMap,liftedWeights_contractible M⟩

end HarmonicArtin

end OAI
