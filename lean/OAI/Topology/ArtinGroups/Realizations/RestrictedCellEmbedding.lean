import Mathlib
import OAI.Topology.ArtinGroups.Realizations.FullSphericalCell
import OAI.Topology.ArtinGroups.Harmonic.PuncturedBoundaryIso

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)
variable (T : Set S) (hT : IsSpherical M T)

noncomputable def restrictedCellEmbedding (g : Artin M) :
    LiftedCell (restrictedMatrix M T) ↪o LiftedCell M where
  toFun a := liftedDeck M g (restrictedLiftedCell M T hT a).val
  inj' := by
    intro a b h
    apply restrictedLiftedCell_injective M T hT
    exact Subtype.ext ((liftedDeck M g).injective h)
  map_rel_iff' := by
    intro a b
    change liftedDeck M g (restrictedLiftedCell M T hT a).val ≤
      liftedDeck M g (restrictedLiftedCell M T hT b).val ↔ a ≤ b
    rw [(liftedDeck M g).le_iff_le,lifted_le_iff_face,lifted_le_iff_face]
    exact restrictedLiftedCell_face_iff M T hT a b

lemma restrictedCellEmbedding_full [Finite (restrictedMatrix M T).Group] (g : Artin M) :
    restrictedCellEmbedding M T hT g (fullSphericalCell (restrictedMatrix M T)) = (g,⟨T,hT⟩) := by
  apply Prod.ext
  · change g * restrictedArtinHom M T 1 = g
    rw [map_one,mul_one]
  · apply Subtype.ext
    change Subtype.val '' (Set.univ : Set T) = T
    ext s
    simp only [Set.mem_image,Set.mem_univ,true_and,Subtype.exists,exists_prop,exists_eq_right]

lemma restrictedCellEmbedding_full_preimage [Finite (restrictedMatrix M T).Group]
    (g : Artin M) (b : LiftedCell M)
    (hb : b ≤ restrictedCellEmbedding M T hT g (fullSphericalCell (restrictedMatrix M T))) :
    ∃ a, restrictedCellEmbedding M T hT g a = b := by
  rw [restrictedCellEmbedding_full] at hb
  obtain ⟨hst,w,hw,_,_,he⟩ := (lifted_le_iff_face M _ _).mp hb
  have hp : g⁻¹*b.1 ∈ artinParabolic M T := by
    rw [he,inv_mul_cancel_left]
    exact wordArtin_mem_parabolic M T w hw
  let v : SphericalLiftedFiber M T := ⟨liftedDeck M g⁻¹ b,hst,hp⟩
  refine ⟨(restrictedLiftedFiberIso M T hT).symm v,?_⟩
  change liftedDeck M g ((restrictedLiftedFiberIso M T hT) ((restrictedLiftedFiberIso M T hT).symm v)).val = b
  rw [OrderIso.apply_symm_apply]
  apply Prod.ext
  · exact mul_inv_cancel_left g b.1
  · rfl

lemma restrictedCellEmbedding_top (g : Artin M) (a : LiftedCell (restrictedMatrix M T)) :
    liftedTopVertex M (restrictedCellEmbedding M T hT g a) =
      g * restrictedArtinHom M T (liftedTopVertex (restrictedMatrix M T) a) := by
  change (g * restrictedArtinHom M T a.1) * positiveLift M
    (sphericalLongest M ⟨Subtype.val '' a.2.val, _⟩) =
      g * restrictedArtinHom M T (a.1 * positiveLift (restrictedMatrix M T) (sphericalLongest (restrictedMatrix M T) a.2))
  rw [←restriction_sphericalLongest M T hT a.2,map_mul,restrictedArtinHom_positiveLift,mul_assoc]

omit [LinearOrder S] in
lemma lifted_same_top_type_unique (a b : LiftedCell M)
    (ht : a.2 = b.2) (hb : liftedTopVertex M a = liftedTopVertex M b) : a = b := by
  apply Prod.ext ?_ ht
  dsimp only [liftedTopVertex] at hb
  rw [ht] at hb
  exact mul_right_cancel hb

end HarmonicArtin

end OAI
