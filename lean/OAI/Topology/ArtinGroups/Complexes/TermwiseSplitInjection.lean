import Mathlib
import OAI.Topology.ArtinGroups.Complexes.PureCoefficientCohomology
import OAI.Topology.ArtinGroups.Complexes.CoefficientSocle
import OAI.Topology.ArtinGroups.Complexes.GeneratorVector

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
variable {I J T : Type*} [Fintype I] [Fintype J] [Fintype T] [DecidableEq I]

structure TermwiseSplitInjection (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) where
  inclusion : Map Q E F
  retraction : Matrix J I (Q.Zigzag K)
  split : inclusion.matrix * retraction = projectiveIdentity Q E.placement

noncomputable def postcomposeOnCycles (E : BasedComplex Q (K := K) T)
    (F : BasedComplex Q (K := K) I) (G : BasedComplex Q (K := K) J)
    (ι : Map Q F G) (n v : ℤ) :
    homCycles Q E F n v →ₗ[K] homCycles Q E G n v where
  toFun f := ⟨f.val * ι.matrix, by
    simpa only [add_zero] using homCycles_mul Q f.property (map_mem_homCycles Q ι)⟩
  map_add' f g := by apply Subtype.ext; exact Matrix.add_mul _ _ _
  map_smul' r f := by apply Subtype.ext; exact Matrix.smul_mul _ _ _

omit [Fintype V] [DecidableEq A] in
lemma postcomposeOnCycles_injective (E : BasedComplex Q (K := K) T)
    (F : BasedComplex Q (K := K) I) (G : BasedComplex Q (K := K) J)
    (ι : TermwiseSplitInjection Q F G) (n v : ℤ) :
    Function.Injective (postcomposeOnCycles Q E F G ι.inclusion n v) := by
  intro f g h
  apply Subtype.ext
  have hh := congrArg (fun f : homCycles Q E G n v => f.val * ι.retraction) h
  change (f.val * ι.inclusion.matrix) * ι.retraction =
    (g.val * ι.inclusion.matrix) * ι.retraction at hh
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ι.split] at hh
  apply Matrix.ext
  intro i j
  have hij := congrArg (fun m : Matrix T I (Q.Zigzag K) => m i j) hh
  simpa only [projectiveIdentity, Matrix.mul_diagonal,
    f.property.1.1.2, g.property.1.1.2] using hij

omit [DecidableEq A] in
lemma pure_coefficient_homDimension_mono (E : BasedComplex Q (K := K) T)
    (F : BasedComplex Q (K := K) I) (G : BasedComplex Q (K := K) J)
    {l k n v : ℤ} (hE : ∀ i, (E.placement i).level = l)
    (hF : ∀ i, (F.placement i).level = k) (hG : ∀ i, (G.placement i).level = k)
    (h : n+v=k-l) (ι : TermwiseSplitInjection Q F G) :
    homDimension Q E F n v ≤ homDimension Q E G n v := by
  unfold homDimension
  rw [(pureCoefficientCohomology Q E F hE hF h).finrank_eq,
    (pureCoefficientCohomology Q E G hE hG h).finrank_eq]
  exact LinearMap.finrank_le_finrank_of_injective
    (postcomposeOnCycles_injective Q E F G ι n v)

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma totalHomDimension_eq_sum_of_subset (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (t : ℤ) (D : Finset ℤ)
    (hD : homInternalSupport Q E F ⊆ D) :
    totalHomDimension Q E F t = ∑ v ∈ D, homDimension Q E F (t-v) v := by
  unfold totalHomDimension
  apply Finset.sum_subset hD
  intro v _ hv
  exact homDimension_off_internal_support Q E F (t-v) v hv

omit [DecidableEq A] in
lemma pure_total_coefficient_homDimension_mono (E : BasedComplex Q (K := K) T)
    (F : BasedComplex Q (K := K) I) (G : BasedComplex Q (K := K) J)
    {l k : ℤ} (hE : ∀ i, (E.placement i).level = l)
    (hF : ∀ i, (F.placement i).level = k) (hG : ∀ i, (G.placement i).level = k)
    (ι : TermwiseSplitInjection Q F G) :
    totalHomDimension Q E F (k-l) ≤ totalHomDimension Q E G (k-l) := by
  classical
  let D := homInternalSupport Q E F ∪ homInternalSupport Q E G
  rw [totalHomDimension_eq_sum_of_subset Q E F (k-l) D Finset.subset_union_left,
    totalHomDimension_eq_sum_of_subset Q E G (k-l) D Finset.subset_union_right]
  apply Finset.sum_le_sum
  intro v _
  exact pure_coefficient_homDimension_mono Q E F G hE hF hG (by omega) ι

lemma subobject_cartan_inequality (M : BasedComplex Q (K := K) J)
    (S : BasedComplex Q (K := K) I) (Y : BasedComplex Q (K := K) T)
    {q d : ℤ} (hM : ∀ i, (M.placement i).level = q)
    (hS : ∀ i, (S.placement i).level = q) (hY : ∀ i, (Y.placement i).level = d)
    (ι : TermwiseSplitInjection Q S M) (active : Set V)
    (hsS : ∀ i, (S.placement i).color ∈ active)
    (hsY : ∀ α ∈ active, ∀ c, coefficientSocle Q Y α c = ⊥)
    (hmid : totalHomDimension Q M Y (d-q+1) = 0) :
    (totalHomDimension Q M Y (d-q) : ℝ) ≤
      (generatorVector Q M - generatorVector Q S) ⬝ᵥ
        ((unfoldedCartan Q).mulVec (generatorVector Q Y)) := by
  rw [sub_dotProduct, pure_cartan_euler Q M Y hM hY, pure_cartan_euler Q S Y hS hY]
  have hz := pure_total_coefficient_homDimension_zero_of_socle_zero Q S Y hS hY active hsS hsY
  have hm := pure_total_coefficient_homDimension_mono Q Y S M hY hS hM ι
  have hm' : (totalHomDimension Q Y S (q-d) : ℝ) ≤ totalHomDimension Q Y M (q-d) := by
    exact_mod_cast hm
  have hn : (0 : ℝ) ≤ totalHomDimension Q S Y (d-q+1) := Nat.cast_nonneg _
  rw [hmid, hz, Nat.cast_zero]
  linarith

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
