import Mathlib
import OAI.RingTheory.Multiplicity.HomogeneousRegradeIdentity
import OAI.RingTheory.Multiplicity.PureProjective
import OAI.RingTheory.Multiplicity.RootBaseProjective

namespace OAI

noncomputable section
namespace Lech.ProjectiveRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open ProductSourceCover
universe u
variable (R : Type u) [CommRing R] (n : ℕ)

def gridSectionsEquiv (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) :
    grid R n m s ∅ ≃ₗ[R] Sections R n s hs m where
  toFun x := ⟨x.val,x.property⟩
  invFun x := ⟨x.val,x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma grid_projective (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) :
    Module.Projective R (grid R n m s ∅) := by
  let := sections_base_projective R n s hs m
  exact Module.Projective.of_equiv (gridSectionsEquiv R n s hs m).symm

lemma zeroAugGrid_projective (s : Finset (Fin (n+1))) (m : Fin n → ℤ) :
    Module.Projective R (AlternatingCech.zeroAugmentation R (GridAmbient R n)
      (fun t => grid R n m t ∅) s) := by
  classical
  by_cases hs : s=∅
  · have he : AlternatingCech.zeroAugmentation R (GridAmbient R n)
        (fun t => grid R n m t ∅) s = ⊥ := by simp [AlternatingCech.zeroAugmentation,hs]
    exact Module.Projective.of_equiv (LinearEquiv.ofEq _ _ he).symm
  · have he : AlternatingCech.zeroAugmentation R (GridAmbient R n)
        (fun t => grid R n m t ∅) s = grid R n m s ∅ := by
          simp [AlternatingCech.zeroAugmentation,hs]
    let := grid_projective R n s (Finset.nonempty_iff_ne_empty.mpr hs) m
    exact Module.Projective.of_equiv (LinearEquiv.ofEq _ _ he).symm

variable [LinearOrder (Chart n)]
omit [LinearOrder (Chart n)] in
lemma target_term_projective (m : Fin n → ℤ) (q : ℕ) :
    Projective ((targetCech R n m).X q) := by
  classical
  let (s : Set.powersetCard (Fin (n+1)) q) := zeroAugGrid_projective R n s.val m
  change Projective (ModuleCat.of R (AlternatingCech.sorted R (GridAmbient R n)
    (AlternatingCech.zeroAugmentation R (GridAmbient R n) (fun t => grid R n m t ∅)) q))
  let : Module.Projective R (AlternatingCech.sorted R (GridAmbient R n)
    (AlternatingCech.zeroAugmentation R (GridAmbient R n) (fun t => grid R n m t ∅)) q) :=
    Module.Projective.of_equiv (DFinsupp.linearEquivFunOnFintype (R:=R))
  exact ModuleCat.projective_of_categoryTheory_projective _

abbrev integerCech (m : Fin n → ℤ) : CochainComplex (ModuleCat.{u} R) ℤ :=
  (targetCech R n m).extend ComplexShape.embeddingUpNat

omit [LinearOrder (Chart n)] in
lemma integer_term_projective (m : Fin n → ℤ) (q : ℤ) :
    Projective ((integerCech R n m).X q) := by
  cases q with
  | ofNat q =>
    let := target_term_projective R n m q
    exact Projective.of_iso ((targetCech R n m).extendXIso ComplexShape.embeddingUpNat (i:=q) rfl).symm inferInstance
  | negSucc q =>
    exact (ComplexExtension.negative_zero (targetCech R n m) q).projective

omit [LinearOrder (Chart n)] in
lemma integer_bounded (m : Fin n → ℤ) : (integerCech R n m).IsStrictlyLE (n+1) := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro q hq
  obtain ⟨j,rfl⟩ := Int.eq_ofNat_of_zero_le (show 0≤q by omega)
  apply IsZero.of_iso _ ((targetCech R n m).extendXIso ComplexShape.embeddingUpNat (i:=j) rfl)
  apply AlternatingCech.sortedComplex_bounded
  simpa only [Fintype.card_fin] using (show n+1<j by omega)

lemma integer_homology_projective (m : Fin n → ℤ) :
    Projective ((integerCech R n m).homology (negativeCount m+1)) := by
  obtain ⟨b⟩ := (targetSigned_pure R n m).2
  let : Module.Free R ((targetCech R n m).homology (negativeCount m+1)) := Module.Free.of_basis b
  apply Projective.of_iso ((targetCech R n m).extendHomologyIso ComplexShape.embeddingUpNat
    (j:=negativeCount m+1) (by simp)).symm
  infer_instance

lemma integer_pure (m : Fin n → ℤ) (q : ℤ) (hq : q≠negativeCount m+1) :
    IsZero ((integerCech R n m).homology q) := by
  cases q with
  | ofNat q =>
    exact ((targetSigned_pure R n m).1 q (by intro h; apply hq; simp only [h]; rfl)).of_iso
      ((targetCech R n m).extendHomologyIso ComplexShape.embeddingUpNat (j:=q) rfl)
  | negSucc q =>
    apply ((integerCech R n m).exactAt_iff_isZero_homology _).mp
    apply ExactAt.of_isZero
    exact ComplexExtension.negative_zero (targetCech R n m) q

 

def integerCechSplitting (m : Fin n → ℤ) :
    HomotopyEquiv ((single (ModuleCat.{u} R) (.up ℤ) (negativeCount m+1)).obj
      ((integerCech R n m).homology (negativeCount m+1))) (integerCech R n m) := by
  letI := integer_homology_projective R n m
  letI := integer_bounded R n m
  letI := integer_term_projective R n m
  exact PureProjective.homotopyEquiv (integerCech R n m) (negativeCount m+1) (n+1)
    (integer_pure R n m)
end Lech.ProjectiveRoot

end

end OAI
