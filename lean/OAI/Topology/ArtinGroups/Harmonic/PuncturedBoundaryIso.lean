import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.LiftedPuncturedBoundary
import OAI.Topology.ArtinGroups.Realizations.RestrictedLiftedCell
import OAI.Topology.ArtinGroups.Realizations.PositiveCellPoset

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable

noncomputable def puncturedBoundaryIso {P Q : Type*} [PartialOrder P] [PartialOrder Q]
    (f : P ↪o Q) (c d : P) (hc : ∀ b ≤ f c, ∃ a, f a = b) :
    {a : P // a < c ∧ a ≠ d} ≃o {b : Q // b < f c ∧ b ≠ f d} where
  toFun a := ⟨f a.val, f.lt_iff_lt.mpr a.property.1,
    fun he => a.property.2 (f.injective he)⟩
  invFun b := ⟨(hc b.val b.property.1.le).choose,
    f.lt_iff_lt.mp (by rw [(hc b.val b.property.1.le).choose_spec]; exact b.property.1),
    fun he => b.property.2 (by rw [←(hc b.val b.property.1.le).choose_spec,he])⟩
  left_inv a := by
    apply Subtype.ext
    exact f.injective (hc (f a.val) (f.monotone a.property.1.le)).choose_spec
  right_inv b := Subtype.ext (hc b.val b.property.1.le).choose_spec
  map_rel_iff' := by intros; exact f.le_iff_le

variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)

noncomputable def positiveCellEmbedding (inj : Function.Injective (positiveToArtin M)) :
    PositiveCellPoset M inj ↪o LiftedCell M where
  toFun := positiveCellToLifted M
  inj' := positiveCellToLifted_injective M inj
  map_rel_iff' := by intros; rfl

omit [Fintype S] [LinearOrder S] in
lemma positiveCellEmbedding_full (inj : Function.Injective (positiveToArtin M))
    (c : PositiveCellPoset M inj) (b : LiftedCell M) (h : b ≤ positiveCellToLifted M c) :
    ∃ a : PositiveCellPoset M inj, positiveCellToLifted M a = b := by
  have hc : positiveCellToLifted M c ∈ PositiveRegion M 1 := ⟨c.1,by simp [positiveCellToLifted]⟩
  obtain ⟨p,hp⟩ := positiveRegion_face_closed M 1 h hc
  refine ⟨(p,b.2),Prod.ext ?_ rfl⟩
  simpa only [positiveCellToLifted,one_mul] using hp.symm

noncomputable def positivePuncturedBoundaryIso (inj : Function.Injective (positiveToArtin M))
    (c d : PositiveCellPoset M inj) :
    {a : PositiveCellPoset M inj // positiveCellToLifted M a < positiveCellToLifted M c ∧ a ≠ d} ≃o
      LiftedPuncturedBoundary M (positiveCellToLifted M c) (positiveCellToLifted M d) :=
  puncturedBoundaryIso (positiveCellEmbedding M inj) c d (positiveCellEmbedding_full M inj c)

omit [LinearOrder S] in
lemma restriction_sphericalLongest (T : Set S) (hT : IsSpherical M T)
    (R : SphericalType (restrictedMatrix M T)) :
    restrictionHom M T (sphericalLongest (restrictedMatrix M T) R) =
      sphericalLongest M ⟨Subtype.val '' R.val, spherical_type_mono M (by rintro _ ⟨s,_,rfl⟩; exact s.property) hT⟩ := by
  let U : SphericalType M := ⟨Subtype.val '' R.val,
    spherical_type_mono M (by rintro _ ⟨s,_,rfl⟩; exact s.property) hT⟩
  apply parabolic_longest_unique M U.val _ _ ?_ (sphericalLongest_spec M U)
  refine ⟨?_,?_⟩
  · rw [show U.val = Subtype.val '' R.val from rfl,←restriction_parabolic_map]
    exact ⟨_,(sphericalLongest_spec (restrictedMatrix M T) R).1,rfl⟩
  · intro w hw
    rw [show U.val = Subtype.val '' R.val from rfl,←restriction_parabolic_map] at hw
    obtain ⟨v,hv,rfl⟩ := hw
    simpa only [restriction_length] using (sphericalLongest_spec (restrictedMatrix M T) R).2 v hv

omit [LinearOrder S] in
lemma restrictedArtinHom_positiveLift (T : Set S) (w : (restrictedMatrix M T).Group) :
    restrictedArtinHom M T (positiveLift (restrictedMatrix M T) w) =
      positiveLift M (restrictionHom M T w) := by
  let v := reducedExpression (restrictedMatrix M T) w
  have hv := reducedExpression_reduced (restrictedMatrix M T) w
  have he := wordCoxeter_reducedExpression (restrictedMatrix M T) w
  have hv' : M.toCoxeterSystem.length (wordCoxeter M (v.map Subtype.val)) = (v.map Subtype.val).length := by
    rw [←restriction_wordCoxeter,restriction_length,List.length_map]
    exact hv
  calc
    _ = wordArtin M (v.map Subtype.val) := by rw [positiveLift,restrictedArtinHom_word]
    _ = positiveLift M (restrictionHom M T w) := by
      rw [←positiveLift_word M _ hv',←restriction_wordCoxeter]
      exact congrArg (fun q => positiveLift M (restrictionHom M T q)) he

end HarmonicArtin

end OAI
