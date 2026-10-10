import OAI.RingTheory.BassTrace.Main

namespace OAI

/-! Canonical trace, augmentation rank and algebraic K₀. -/

open scoped Classical BigOperators
noncomputable section
namespace TorsionFreeBass

/-- A group is torsion-free when its only finite-order element is the identity.
This is the usual group-theoretic condition, not the stronger unique-roots condition. -/
def TorsionFree (G : Type*) [Group G] : Prop := ∀ g : G, IsOfFinOrder g → g = 1

variable {G : Type*} [Group G]

/-- The sum of coefficients, or augmentation, of the complex group algebra. -/
def augmentation : MonoidAlgebra ℂ G →+* ℂ :=
  (MonoidAlgebra.lift ℂ ℂ G (1 : G →* ℂ)).toRingHom

lemma augmentation_apply (a : MonoidAlgebra ℂ G) :
    augmentation a = a.coeff.sum (fun _ z => z) := by
  simp [augmentation, MonoidAlgebra.lift_apply]

/-- The canonical trace is the coefficient of the identity. -/
def canonicalTrace (a : MonoidAlgebra ℂ G) : ℂ := a.coeff 1

/-- The matrix trace obtained by applying the canonical trace to each diagonal entry. -/
def matrixTrace {q : ℕ} (e : Matrix (Fin q) (Fin q) (MonoidAlgebra ℂ G)) : ℂ :=
  ∑ i, canonicalTrace (e i i)

/-- Entrywise augmentation. -/
def augmentedMatrix {m n : ℕ} (e : Matrix (Fin m) (Fin n) (MonoidAlgebra ℂ G)) :
    Matrix (Fin m) (Fin n) ℂ := e.map augmentation

lemma canonicalTrace_eq_classCoefficient (a : MonoidAlgebra ℂ G) :
    canonicalTrace a = BassTrace.classCoefficient 1 a := by
  simp [canonicalTrace, BassTrace.classCoefficient]

lemma matrixTrace_eq_classCoefficient {q : ℕ}
    (e : Matrix (Fin q) (Fin q) (MonoidAlgebra ℂ G)) :
    matrixTrace e = BassTrace.classCoefficient 1 (Matrix.trace e) := by
  simp [matrixTrace, Matrix.trace, Matrix.diag, canonicalTrace_eq_classCoefficient]

lemma augmentedMatrix_mul {m n p : ℕ}
    (a : Matrix (Fin m) (Fin n) (MonoidAlgebra ℂ G))
    (b : Matrix (Fin n) (Fin p) (MonoidAlgebra ℂ G)) :
    augmentedMatrix (a * b) = augmentedMatrix a * augmentedMatrix b := by
  exact Matrix.map_mul

lemma augmentedMatrix_trace {q : ℕ}
    (e : Matrix (Fin q) (Fin q) (MonoidAlgebra ℂ G)) :
    Matrix.trace (augmentedMatrix e) = augmentation (Matrix.trace e) := by
  simp [augmentedMatrix, Matrix.trace, Matrix.diag]

lemma idempotent_matrix_trace_eq_rank {q : ℕ} (a : Matrix (Fin q) (Fin q) ℂ)
    (ha : a * a = a) : Matrix.trace a = (a.rank : ℂ) := by
  have h : IsIdempotentElem a.toLin' := by
    change a.toLin'.comp a.toLin' = a.toLin'
    rw [← Matrix.toLin'_mul, ha]
  rw [← Matrix.trace_toLin'_eq, (LinearMap.IsIdempotentElem.isProj_range _ h).trace]
  rfl

lemma classTrace_sum (a : MonoidAlgebra ℂ G) :
    (BassTrace.K0.classTrace a).sum (fun _ z => z) = augmentation a := by
  rw [augmentation_apply]
  simp [BassTrace.K0.classTrace, Finsupp.sum_mapDomain_index]

/-- Bass support reduces to the identity conjugacy class in a torsion-free group. -/
lemma matrix_trace_eq_augmentation (hG : TorsionFree G) {q : ℕ}
    (e : Matrix (Fin q) (Fin q) (MonoidAlgebra ℂ G)) (he : e * e = e) :
    matrixTrace e = augmentation (Matrix.trace e) := by
  let tr := BassTrace.K0.classTrace (Matrix.trace e)
  have htr (c : ConjClasses G) (hc : c ≠ ConjClasses.mk 1) : tr c = 0 := by
    obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
    rw [BassTrace.K0.classTrace_apply]
    apply BassTrace.bassTrace e he g
    intro hg
    exact hc (congrArg ConjClasses.mk (hG g hg))
  rw [matrixTrace_eq_classCoefficient, ← BassTrace.K0.classTrace_apply,
    ← classTrace_sum]
  symm
  apply Finsupp.sum_eq_single (ConjClasses.mk (1 : G))
  · intro c _ hc
    exact htr c hc
  · simp

/-- The matrix assertion holds also for the empty matrix. -/
theorem matrix_trace_eq_rank (hG : TorsionFree G) {q : ℕ}
    (e : Matrix (Fin q) (Fin q) (MonoidAlgebra ℂ G)) (he : e * e = e) :
    matrixTrace e = ((augmentedMatrix e).rank : ℂ) := by
  rw [matrix_trace_eq_augmentation hG e he, ← augmentedMatrix_trace]
  apply idempotent_matrix_trace_eq_rank
  rw [← augmentedMatrix_mul, he]


open BassTrace.K0 in
/-- The augmentation rank on the free abelian group of idempotents, before imposing
isomorphism and direct-sum relations. -/
def rawAugmentationRank : FreeAbelianGroup (Idempotent (MonoidAlgebra ℂ G)) →+ ℤ :=
  FreeAbelianGroup.lift (fun e => ((augmentedMatrix e.matrix).rank : ℤ))

lemma rawAugmentationRank_of (e : BassTrace.K0.Idempotent (MonoidAlgebra ℂ G)) :
    ((rawAugmentationRank (FreeAbelianGroup.of e) : ℤ) : ℂ) =
      augmentation (Matrix.trace e.matrix) := by
  change (((augmentedMatrix e.matrix).rank : ℤ) : ℂ) = _
  rw [Int.cast_natCast, ← idempotent_matrix_trace_eq_rank]
  · exact augmentedMatrix_trace _
  · rw [← augmentedMatrix_mul, e.idem]

lemma augmentationRank_relations : BassTrace.K0.relations (MonoidAlgebra ℂ G) ≤
    (rawAugmentationRank (G := G)).ker := by
  apply (AddSubgroup.closure_le _).mpr
  intro x hx
  rcases hx with ⟨e,f,a,b,hab,hba,rfl⟩ | ⟨e,f,rfl⟩
  · change rawAugmentationRank (FreeAbelianGroup.of e - FreeAbelianGroup.of f) = 0
    apply Int.cast_injective (α := ℂ)
    rw [map_sub, Int.cast_sub, rawAugmentationRank_of, rawAugmentationRank_of, Int.cast_zero]
    apply sub_eq_zero.mpr
    rw [← augmentedMatrix_trace, ← augmentedMatrix_trace, ← hab, ← hba,
      augmentedMatrix_mul, augmentedMatrix_mul]
    exact Matrix.trace_mul_comm _ _
  · change rawAugmentationRank (FreeAbelianGroup.of (BassTrace.K0.directSum e f) -
      FreeAbelianGroup.of e - FreeAbelianGroup.of f) = 0
    apply Int.cast_injective (α := ℂ)
    simp only [map_sub, Int.cast_sub, rawAugmentationRank_of, Int.cast_zero,
      BassTrace.K0.trace_directSum, map_add]
    abel

/-- The integer-valued augmentation rank on the usual idempotent presentation of
algebraic K₀: on a generator it is the complex dimension of the augmented image. -/
def augmentationRank : BassTrace.K0.Group (MonoidAlgebra ℂ G) →+ ℤ :=
  QuotientAddGroup.lift (BassTrace.K0.relations (MonoidAlgebra ℂ G))
    rawAugmentationRank augmentationRank_relations

lemma augmentationRank_classOf (e : BassTrace.K0.Idempotent (MonoidAlgebra ℂ G)) :
    augmentationRank (BassTrace.K0.classOf e) = (augmentedMatrix e.matrix).rank := by
  simp [augmentationRank, BassTrace.K0.classOf, rawAugmentationRank]

open BassTrace.K0 in
lemma traceK0_relations : relations (MonoidAlgebra ℂ G) ≤ (rawCoefficient (1 : G)).ker := by
  apply (AddSubgroup.closure_le _).mpr
  intro element membership
  rcases membership with
    ⟨idemLeft, idemRight, forward, backward, forward_backward, backward_forward, rfl⟩ |
    ⟨idemLeft, idemRight, rfl⟩
  · change rawCoefficient 1 (FreeAbelianGroup.of idemLeft - FreeAbelianGroup.of idemRight) = 0
    rw [map_sub]
    apply sub_eq_zero.mpr
    simp only [rawCoefficient, FreeAbelianGroup.lift_apply_of]
    rw [← forward_backward, ← backward_forward]
    exact BassTrace.classCoefficient_matrix_mul_comm 1 forward backward
  · change rawCoefficient 1 (FreeAbelianGroup.of (directSum idemLeft idemRight) -
      FreeAbelianGroup.of idemLeft - FreeAbelianGroup.of idemRight) = 0
    rw [map_sub, map_sub]
    simp only [rawCoefficient, FreeAbelianGroup.lift_apply_of]
    rw [trace_directSum, BassTrace.classCoefficient_add, add_sub_cancel_left, sub_self]

/-- Coefficient at the identity class of the Hattori--Stallings trace on K₀. -/
def traceK0 : BassTrace.K0.Group (MonoidAlgebra ℂ G) →+ ℂ :=
  QuotientAddGroup.lift (BassTrace.K0.relations (MonoidAlgebra ℂ G))
    (BassTrace.K0.rawCoefficient 1) traceK0_relations

lemma traceK0_classOf (e : BassTrace.K0.Idempotent (MonoidAlgebra ℂ G)) :
    traceK0 (BassTrace.K0.classOf e) = matrixTrace e.matrix := by
  exact (BassTrace.K0.hsCoefficient_classOf 1 e).trans (matrixTrace_eq_classCoefficient _).symm

/-- The maps agree, with the integers included in the complex numbers. -/
theorem traceK0_eq_augmentationRank (hG : TorsionFree G) :
    traceK0 (G := G) = (Int.castAddHom ℂ).comp augmentationRank := by
  apply AddMonoidHom.ext
  intro x
  induction x using QuotientAddGroup.induction_on with | H z =>
    change BassTrace.K0.rawCoefficient 1 z = (rawAugmentationRank z : ℂ)
    induction z using FreeAbelianGroup.induction_on with
    | zero => simp only [map_zero, Int.cast_zero]
    | of e =>
      simp only [BassTrace.K0.rawCoefficient, rawAugmentationRank,
        FreeAbelianGroup.lift_apply_of, Int.cast_natCast]
      rw [← matrixTrace_eq_classCoefficient]
      exact matrix_trace_eq_rank hG e.matrix e.idem
    | neg z hz => simp only [map_neg, Int.cast_neg, hz]
    | add z w hz hw => simp only [map_add, Int.cast_add, hz, hw]

/-- The free module of rank one, represented by the one by one identity matrix. -/
def unitIdempotent : BassTrace.K0.Idempotent (MonoidAlgebra ℂ G) where
  size := 1
  matrix := 1
  idem := one_mul _

lemma traceK0_unit : traceK0 (BassTrace.K0.classOf (unitIdempotent (G := G))) = 1 := by
  rw [traceK0_classOf]
  change matrixTrace (1 : Matrix (Fin 1) (Fin 1) (MonoidAlgebra ℂ G)) = 1
  simp [matrixTrace, canonicalTrace]

/-- Its image is exactly the subgroup of integers. -/
theorem traceK0_range (hG : TorsionFree G) :
    Set.range (traceK0 (G := G)) = Set.range (fun z : ℤ => (z : ℂ)) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, rfl⟩
    exact ⟨augmentationRank x, by rw [traceK0_eq_augmentationRank hG]; rfl⟩
  · rintro _ ⟨z, rfl⟩
    refine ⟨z • BassTrace.K0.classOf (unitIdempotent (G := G)), ?_⟩
    rw [map_zsmul, traceK0_unit]
    simp

end TorsionFreeBass
end

end OAI
