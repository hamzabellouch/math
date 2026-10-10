import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.PrincipalOrderIso

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric Topology

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type*} [Fintype S] [DecidableEq S] (M : CoxeterMatrix S)

noncomputable def liftedFaceChart (a : LiftedCell M) :
    CoxeterCellFace (restrictedMatrix M a.2.val) ≃o Set.Iic a :=
  (sourceCellFaceIso M a.2).trans (sourcePrincipalDeck M a)

noncomputable def liftedFaceEmbedding (a : LiftedCell M) :
    CoxeterCellFace (restrictedMatrix M a.2.val) →o LiftedCell M :=
  (weightInclusion (Set.Iic a)).comp
    (liftedFaceChart M a : CoxeterCellFace (restrictedMatrix M a.2.val) →o Set.Iic a)

lemma liftedFaceEmbedding_source (a : LiftedCell M)
    (c : CoxeterCellFace (restrictedMatrix M a.2.val)) :
    (liftedFaceEmbedding M a c).1=a.1*positiveLift M (restrictionHom M a.2.val c.val.1) := rfl

lemma liftedFaceEmbedding_type (a : LiftedCell M)
    (c : CoxeterCellFace (restrictedMatrix M a.2.val)) :
    (liftedFaceEmbedding M a c).2.val=Subtype.val '' c.val.2 := rfl

noncomputable def geometricFaceInclusion {a b : LiftedCell M} (h : a ≤ b) :
    CoxeterCellFace (restrictedMatrix M a.2.val) →o CoxeterCellFace (restrictedMatrix M b.2.val) :=
  ((liftedFaceChart M b).symm : Set.Iic b →o CoxeterCellFace (restrictedMatrix M b.2.val)).comp
    ((weightSubset (Set.Iic a) (Set.Iic b) (fun _ hx => hx.trans h)).comp
      (liftedFaceChart M a : CoxeterCellFace (restrictedMatrix M a.2.val) →o Set.Iic a))

lemma geometricFaceInclusion_embeds {a b : LiftedCell M} (h : a ≤ b)
    (c : CoxeterCellFace (restrictedMatrix M a.2.val)) :
    liftedFaceEmbedding M b (geometricFaceInclusion M h c)=liftedFaceEmbedding M a c := by
  exact congrArg Subtype.val ((liftedFaceChart M b).apply_symm_apply
    (⟨(liftedFaceChart M a c).val,(liftedFaceChart M a c).property.trans h⟩ : Set.Iic b))

lemma geometricFaceInclusion_injective {a b : LiftedCell M} (h : a ≤ b) :
    Function.Injective (geometricFaceInclusion M h) := by
  intro c d he
  apply (liftedFaceChart M a).injective
  apply Subtype.val_injective
  change liftedFaceEmbedding M a c=liftedFaceEmbedding M a d
  rw [←geometricFaceInclusion_embeds M h c,←geometricFaceInclusion_embeds M h d,he]

lemma geometricFaceInclusion_labels {a b : LiftedCell M} (h : a ≤ b)
    (c : CoxeterCellFace (restrictedMatrix M a.2.val)) :
    artinCoxeter M b.1 * restrictionHom M b.2.val (geometricFaceInclusion M h c).val.1 =
      artinCoxeter M a.1 * restrictionHom M a.2.val c.val.1 ∧
    Subtype.val '' (geometricFaceInclusion M h c).val.2 = Subtype.val '' c.val.2 := by
  have he := geometricFaceInclusion_embeds M h c
  refine ⟨?_,congrArg (fun p : LiftedCell M => p.2.val) he⟩
  have hs := congrArg (fun p : LiftedCell M => artinCoxeter M p.1) he
  simp only [liftedFaceEmbedding_source,map_mul,artinCoxeter_positiveLift] at hs
  exact hs

lemma sourceCellMap_barycentric (a : LiftedCell M)
    (w : OrderWeights (CoxeterCellFace (restrictedMatrix M a.2.val))) :
    sourceCellMap M a (permutahedronBarycentricHomeomorph (restrictedMatrix M a.2.val) w)=
      weightMap (liftedFaceEmbedding M a) w := by
  simp only [sourceCellMap,ContinuousMap.comp_apply,ContinuousMap.coe_mk,
    liftedModelHomeomorph,sourceModelHomeomorph,Homeomorph.trans_apply,
    Homeomorph.symm_apply_apply]
  change weightMap (weightInclusion (Set.Iic a))
    (weightMap (sourcePrincipalDeck M a : Set.Iic ((1,a.2) : LiftedCell M) →o Set.Iic a)
      (weightMap (sourceCellFaceIso M a.2 :
        CoxeterCellFace (restrictedMatrix M a.2.val) →o Set.Iic ((1,a.2) : LiftedCell M)) w))=_
  rw [weightMap_comp,weightMap_comp]
  rfl

lemma sourceModelFaceMap_barycentric {a b : LiftedCell M} (h : a ≤ b)
    (w : OrderWeights (CoxeterCellFace (restrictedMatrix M a.2.val))) :
    sourceModelFaceMap M h (permutahedronBarycentricHomeomorph (restrictedMatrix M a.2.val) w)=
      permutahedronBarycentricHomeomorph (restrictedMatrix M b.2.val)
        (weightMap (geometricFaceInclusion M h) w) := by
  apply sourceCellMap_injective M b
  rw [sourceModelFaceMap_included,sourceCellMap_barycentric,sourceCellMap_barycentric,weightMap_comp]
  congr 1
  apply OrderHom.ext
  funext c
  exact (geometricFaceInclusion_embeds M h c).symm

lemma sourceModelFaceMap_affine {a b : LiftedCell M} (h : a ≤ b)
    (w : OrderWeights (CoxeterCellFace (restrictedMatrix M a.2.val))) :
    (sourceModelFaceMap M h (permutahedronBarycentricHomeomorph (restrictedMatrix M a.2.val) w)).val =
      weightAffineValue (fun c => faceCenter (restrictedMatrix M b.2.val) (geometricFaceInclusion M h c)) w := by
  rw [sourceModelFaceMap_barycentric,permutahedronBarycentricHomeomorph_apply]
  exact Finsupp.linearCombination_mapDomain _ _ _

end HarmonicArtin

end OAI
