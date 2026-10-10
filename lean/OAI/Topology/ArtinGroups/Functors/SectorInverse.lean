import Mathlib
import OAI.Topology.ArtinGroups.Functors.Evaluation

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.StringFunctor
variable {V B J K : Type*} (Q : ReversibleQuiver V B)
  (step : B → Bool) (hstep : ∀ b, step (Q.reverse b) = step b)
  (N : J → J → Prop) (hN : ∀ ⦃first second⦄, N first second → N second first)
  [Fintype V] [Fintype B] [Fintype J]
  [DecidableEq V] [DecidableEq B] [DecidableEq J] [DecidableRel N] [Field K]
  (orient : B → Bool) (μ : J → K) (A : K)

local notation "U" => Q.stringQuiver step hstep N hN

noncomputable def sectorInverse (u t : V) (b c : J)
    (d : (p : Zigzag.CornerPath Q u t) × PathRight step N p.val b c)
    (a : (p : Zigzag.CornerPath Q u t) × PathLeft step N p.val b c) : K := by
  classical
  exact if h : d.1=a.1 then pathUnswitch step N orient μ A a.1.val b c (h ▸ d.2) a.2 else 0

noncomputable def inverseEvaluationMatrix (u t : V) (b c : J) :
    Matrix (RightPaths Q step hstep N hN u t b c)
      (LeftPaths Q step hstep N hN u t b c) K :=
  fun y x => sectorInverse Q step N orient μ A u t b c
    (rightPathsEquiv Q step hstep N hN u t b c y)
    (leftPathsEquiv Q step hstep N hN u t b c x)

omit [Fintype V] [Fintype B] [Fintype J] [DecidableRel N] in
lemma inverseEvaluationMatrix_sector (u t : V) (b c : J)
    (p q : Zigzag.CornerPath Q u t) (d : PathRight step N p.val b c)
    (a : PathLeft step N q.val b c) :
    inverseEvaluationMatrix Q step hstep N hN orient μ A u t b c
      ((rightPathsEquiv Q step hstep N hN u t b c).symm ⟨p,d⟩)
      ((leftPathsEquiv Q step hstep N hN u t b c).symm ⟨q,a⟩) =
      if h : p=q then pathUnswitch step N orient μ A q.val b c (h ▸ d) a else 0 := by
  simp only [inverseEvaluationMatrix,Equiv.apply_symm_apply]
  rfl

omit [Fintype V] [Fintype B] [DecidableEq V] [DecidableEq B] in
lemma linearSwitch_symm_sector (hμ : ∀ a, μ a ≠ 0) (δ : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
    (u t : V) (b c : J) (x : RightPaths Q step hstep N hN u t b c → K)
    (p : Zigzag.CornerPath Q u t) (a : PathLeft step N p.val b c) :
    (linearSwitch Q step hstep N hN orient μ A hμ δ hA hroot hPF u t b c).symm x
      ((leftPathsEquiv Q step hstep N hN u t b c).symm ⟨p,a⟩) =
      ∑ d : PathRight step N p.val b c,
        x ((rightPathsEquiv Q step hstep N hN u t b c).symm ⟨p,d⟩) *
          pathUnswitch step N orient μ A p.val b c d a := by
  change Sigma.uncurry
    ((LinearEquiv.piCongrRight (fun p : Zigzag.CornerPath Q u t =>
      pathSwitchEquiv step N hN orient μ A hμ δ hA hroot hPF p.val b c)).symm
        (rightSectors Q step hstep N hN u t b c x))
    ((leftPathsEquiv Q step hstep N hN u t b c)
      ((leftPathsEquiv Q step hstep N hN u t b c).symm ⟨p,a⟩)) = _
  rw [Equiv.apply_symm_apply]
  rfl

lemma inverseEvaluationMatrix_vecMul (hμ : ∀ a, μ a ≠ 0) (δ : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
    (u t : V) (b c : J) (x : RightPaths Q step hstep N hN u t b c → K) :
    Matrix.vecMul x (inverseEvaluationMatrix Q step hstep N hN orient μ A u t b c) =
      (linearSwitch Q step hstep N hN orient μ A hμ δ hA hroot hPF u t b c).symm x := by
  classical
  funext y
  obtain ⟨⟨q,a⟩,rfl⟩ := (leftPathsEquiv Q step hstep N hN u t b c).symm.surjective y
  rw [linearSwitch_symm_sector]
  change (∑ z, x z * inverseEvaluationMatrix Q step hstep N hN orient μ A u t b c z _) = _
  rw [← (rightPathsEquiv Q step hstep N hN u t b c).symm.sum_comp]
  rw [Fintype.sum_sigma,Finset.sum_eq_single q]
  · apply Finset.sum_congr rfl
    intro d hd
    rw [inverseEvaluationMatrix_sector,dite_eq_left rfl]
  · intro p hp hpq
    apply Finset.sum_eq_zero
    intro d hd
    rw [inverseEvaluationMatrix_sector,dite_eq_right hpq,mul_zero]
  · simp

lemma evaluationMatrix_inverse (hμ : ∀ a, μ a ≠ 0) (δ : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
    (u t : V) (b c : J) :
    evaluationMatrix Q step hstep N hN orient μ A u t b c *
      inverseEvaluationMatrix Q step hstep N hN orient μ A u t b c = (by classical exact 1) := by
  classical
  apply Matrix.vecMul_injective
  funext x
  dsimp only
  rw [← Matrix.vecMul_vecMul,
    evaluationMatrix_vecMul Q step hstep N hN orient μ A hμ δ hA hroot hPF,
    inverseEvaluationMatrix_vecMul Q step hstep N hN orient μ A hμ δ hA hroot hPF,
    LinearEquiv.symm_apply_apply,Matrix.vecMul_one]

lemma inverseEvaluationMatrix_inverse (hμ : ∀ a, μ a ≠ 0) (δ : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
    (u t : V) (b c : J) :
    inverseEvaluationMatrix Q step hstep N hN orient μ A u t b c *
      evaluationMatrix Q step hstep N hN orient μ A u t b c = (by classical exact 1) := by
  classical
  apply Matrix.vecMul_injective
  funext x
  dsimp only
  rw [← Matrix.vecMul_vecMul,
    inverseEvaluationMatrix_vecMul Q step hstep N hN orient μ A hμ δ hA hroot hPF,
    evaluationMatrix_vecMul Q step hstep N hN orient μ A hμ δ hA hroot hPF,
    LinearEquiv.apply_symm_apply,Matrix.vecMul_one]

lemma evaluationMatrix_length {u t : V} {b c : J}
    (x : LeftPaths Q step hstep N hN u t b c)
    (y : RightPaths Q step hstep N hN u t b c)
    (h : evaluationMatrix Q step hstep N hN orient μ A u t b c x y ≠ 0) :
    Path.length x.2.val = Path.length y.2.val := by
  by_contra hn
  exact h ((Zigzag.coordinates_homogeneous U _ _).1
    (linearMap_homogeneous Q step hstep N hN orient μ A (Zigzag.pathBasis_homogeneous U x.2.val)
      (evaluationSource N u c x.1) (evaluationTarget N t b y.1)) y.2.val (Ne.symm hn))

omit [Fintype V] [Fintype B] [Fintype J] [DecidableRel N] in
lemma inverseEvaluationMatrix_length {u t : V} {b c : J}
    (y : RightPaths Q step hstep N hN u t b c)
    (x : LeftPaths Q step hstep N hN u t b c)
    (h : inverseEvaluationMatrix Q step hstep N hN orient μ A u t b c y x ≠ 0) :
    Path.length y.2.val = Path.length x.2.val := by
  classical
  unfold inverseEvaluationMatrix sectorInverse at h
  split_ifs at h with he
  · have hf := congrArg (fun p : Zigzag.CornerPath Q u t => Path.length p.val) he
    change Path.length (basePath step N y.2.val) = Path.length (basePath step N x.2.val) at hf
    simpa only [basePath_length] using hf
  · exact (h rfl).elim

end HarmonicArtin.ReversibleQuiver.StringFunctor

end OAI
