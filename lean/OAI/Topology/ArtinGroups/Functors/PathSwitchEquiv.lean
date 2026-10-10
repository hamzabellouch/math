import Mathlib
import OAI.Topology.ArtinGroups.Functors.BasePath

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.StringFunctor
variable {V B J K : Type*} (Q : ReversibleQuiver V B)
  (step : B → Bool) (hstep : ∀ b, step (Q.reverse b) = step b)
  (N : J → J → Prop) (hN : ∀ ⦃first second⦄, N first second → N second first)
  [Fintype V] [Fintype B] [Fintype J]
  [DecidableEq V] [DecidableEq B] [DecidableEq J] [DecidableRel N] [Field K]
  (orient : B → Bool) (μ : J → K) (A : K)

noncomputable def pathSwitchEquiv (hμ : ∀ a, μ a ≠ 0) (δ : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
    (p : Path V B) (b c : J) :
    (PathLeft step N p b c → K) ≃ₗ[K] (PathRight step N p b c → K) where
  toFun := fun x => Matrix.vecMul x (pathSwitch step N orient μ A p b c)
  invFun := fun y => Matrix.vecMul y (pathUnswitch step N orient μ A p b c)
  left_inv x := by
    dsimp only
    rw [Matrix.vecMul_vecMul,pathSwitch_inverse step N hN orient μ A hμ δ hA hroot hPF,
      Matrix.vecMul_one]
  right_inv x := by
    dsimp only
    rw [Matrix.vecMul_vecMul,pathUnswitch_inverse step N hN orient μ A hμ δ hA hroot hPF,
      Matrix.vecMul_one]
  map_add' x y := Matrix.add_vecMul _ x y
  map_smul' a x := Matrix.smul_vecMul a x _

noncomputable def leftSectors (u t : V) (b c : J) :
    (LeftPaths Q step hstep N hN u t b c → K) ≃ₗ[K]
      ((p : Zigzag.CornerPath Q u t) → PathLeft step N p.val b c → K) where
  toFun x p a := x ((leftPathsEquiv Q step hstep N hN u t b c).symm ⟨p,a⟩)
  invFun x a := Sigma.uncurry x (leftPathsEquiv Q step hstep N hN u t b c a)
  left_inv x := by
    funext a
    change x ((leftPathsEquiv Q step hstep N hN u t b c).symm
      (leftPathsEquiv Q step hstep N hN u t b c a)) = x a
    rw [Equiv.symm_apply_apply]
  right_inv x := by
    funext p a
    change Sigma.uncurry x ((leftPathsEquiv Q step hstep N hN u t b c)
      ((leftPathsEquiv Q step hstep N hN u t b c).symm ⟨p,a⟩)) = x p a
    rw [Equiv.apply_symm_apply]
    rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def rightSectors (u t : V) (b c : J) :
    (RightPaths Q step hstep N hN u t b c → K) ≃ₗ[K]
      ((p : Zigzag.CornerPath Q u t) → PathRight step N p.val b c → K) where
  toFun x p a := x ((rightPathsEquiv Q step hstep N hN u t b c).symm ⟨p,a⟩)
  invFun x a := Sigma.uncurry x (rightPathsEquiv Q step hstep N hN u t b c a)
  left_inv x := by
    funext a
    change x ((rightPathsEquiv Q step hstep N hN u t b c).symm
      (rightPathsEquiv Q step hstep N hN u t b c a)) = x a
    rw [Equiv.symm_apply_apply]
  right_inv x := by
    funext p a
    change Sigma.uncurry x ((rightPathsEquiv Q step hstep N hN u t b c)
      ((rightPathsEquiv Q step hstep N hN u t b c).symm ⟨p,a⟩)) = x p a
    rw [Equiv.apply_symm_apply]
    rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def linearSwitch (hμ : ∀ a, μ a ≠ 0) (δ : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
    (u t : V) (b c : J) :
    (LeftPaths Q step hstep N hN u t b c → K) ≃ₗ[K]
      (RightPaths Q step hstep N hN u t b c → K) :=
  (leftSectors Q step hstep N hN u t b c).trans
    ((LinearEquiv.piCongrRight (fun p : Zigzag.CornerPath Q u t =>
      pathSwitchEquiv step N hN orient μ A hμ δ hA hroot hPF p.val b c)).trans
        (rightSectors Q step hstep N hN u t b c).symm)

omit [Fintype V] [Fintype B] [DecidableEq V] [DecidableEq B] in
lemma linearSwitch_sector (hμ : ∀ a, μ a ≠ 0) (δ : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
    (u t : V) (b c : J) (x : LeftPaths Q step hstep N hN u t b c → K)
    (p : Zigzag.CornerPath Q u t) (d : PathRight step N p.val b c) :
    linearSwitch Q step hstep N hN orient μ A hμ δ hA hroot hPF u t b c x
      ((rightPathsEquiv Q step hstep N hN u t b c).symm ⟨p,d⟩) =
      ∑ a : PathLeft step N p.val b c,
        x ((leftPathsEquiv Q step hstep N hN u t b c).symm ⟨p,a⟩) *
          pathSwitch step N orient μ A p.val b c a d := by
  change Sigma.uncurry
    ((LinearEquiv.piCongrRight (fun p : Zigzag.CornerPath Q u t =>
      pathSwitchEquiv step N hN orient μ A hμ δ hA hroot hPF p.val b c))
        (leftSectors Q step hstep N hN u t b c x))
    ((rightPathsEquiv Q step hstep N hN u t b c)
    ((rightPathsEquiv Q step hstep N hN u t b c).symm ⟨p,d⟩)) = _
  rw [Equiv.apply_symm_apply]
  rfl

end HarmonicArtin.ReversibleQuiver.StringFunctor

end OAI
