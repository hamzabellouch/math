import OAI.Topology.ArtinGroups.ParabolicIntersections.TokenBoundary
import OAI.Topology.ArtinGroups.ParabolicIntersections.PathImages

namespace OAI

/-! Incoming spanning inside a cochain interval, used to force an empty placement. -/
namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A : Type} (Q : ReversibleQuiver V A) [Fintype V] [Fintype A]
  {I : Type} [Fintype I]

/-- If the next higher layer is absent, exactness expresses every basis
vector through incoming arrows in the same layer. Iterated path images
record this statement without losing possible linear cancellations. -/
theorem incoming_spanning_step (E : BasedComplex Q (K := ℂ) I) (hE : E.IsMinimal Q)
    (l r : ℤ) (i : {i | l ≤ (E.placement i).cochain ∧ (E.placement i).cochain ≤ r})
    (hil : l < (E.placement i).cochain)
    (hex : ScalarExactAt Q (E.testComplex Q (E.placement i).color)
      (E.placement i).color ((E.placement i).level+2) (E.placement i).cochain)
    (hhigher : ∀ j, (E.placement j).cochain = (E.placement i).cochain-1 →
      (E.placement i).level < (E.placement j).level → False)
    (n : ℕ)
    (hprev : ∀ j : {j | l ≤ (E.placement j).cochain ∧ (E.placement j).cochain ≤ r},
      (E.placement j).level = (E.placement i).level →
      (E.placement j).cochain = (E.placement i).cochain-1 →
      Pi.single j (1 : ℂ) ∈ pathImages (arrowMatrix Q (cochainInterval Q E l r)) n) :
    Pi.single i (1 : ℂ) ∈ pathImages (arrowMatrix Q (cochainInterval Q E l r)) (n+1) := by
  let J := {j | l ≤ (E.placement j).cochain ∧ (E.placement j).cochain ≤ r}
  let B := arrowMatrix Q (cochainInterval Q E l r)
  obtain ⟨y, hy, he⟩ := generator_token_boundary Q E hE i.val hex
  let z (u : TestIndex Q E.placement (E.placement i).color) : J → ℂ :=
    fun j => y u * pathCoordinates Q (E.differential u.1 j.val) (Path.dual Q u.2.val)
  have heq : (Pi.single i (1 : ℂ) : J → ℂ) = ∑ u, z u := by
    funext j
    rw [Finset.sum_apply]
    change (Pi.single i (1 : ℂ) : J → ℂ) j = ∑ u, y u * _
    have h := he j.val
    simpa only [Pi.single_apply, Subtype.val_inj] using h
  rw [heq]
  apply Submodule.sum_mem
  intro u _
  by_cases hzero : y u = 0
  · have hz : z u = 0 := by
      ext j
      change y u * _ = 0
      rw [hzero, MulZeroClass.zero_mul]
    rw [hz]
    exact Submodule.zero_mem _
  obtain ⟨hdeg, hlev⟩ := hy u hzero
  rcases hp : u.2.val with v | a | v
  · have hlen : Path.length u.2.val = 0 := by rw [hp]; rfl
    have hh : (E.placement i).level < (E.placement u.1).level := by omega
    exact (hhigher u.1 hdeg hh).elim
  · have hlen : Path.length u.2.val = 1 := by rw [hp]; rfl
    have hu : l ≤ (E.placement u.1).cochain ∧ (E.placement u.1).cochain ≤ r := by
      have hir := i.property.2
      constructor <;> omega
    let j₀ : J := ⟨u.1, hu⟩
    have hj₀ : Pi.single j₀ (1 : ℂ) ∈ pathImages B n := hprev j₀ (by
      change (E.placement u.1).level = (E.placement i).level
      omega) hdeg
    have hz : z u = y u • Matrix.vecMul (Pi.single j₀ (1 : ℂ)) (B (Q.reverse a)) := by
      funext j
      change y u * pathCoordinates Q (E.differential u.1 j.val) (Path.dual Q u.2.val) = _
      rw [hp]
      change y u * (E.differential u.1 j.val).arrow (Q.reverse a) = _
      simp only [Pi.smul_apply, smul_eq_mul, Matrix.vecMul, dotProduct, Pi.single_apply,
        ite_mul, _root_.one_mul, MulZeroClass.zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      rfl
    rw [hz]
    exact Submodule.smul_mem _ _ (pathImages_step B hj₀ (Q.reverse a))
  · have hz : z u = 0 := by
      funext j
      change y u * pathCoordinates Q (E.differential u.1 j.val) (Path.dual Q u.2.val) = 0
      rw [hp]
      change y u * (E.differential u.1 j.val).vertex v = 0
      rw [hE u.1 j.val]
      exact MulZeroClass.mul_zero _
    rw [hz]
    exact Submodule.zero_mem _

end HarmonicArtin.ParabolicIntersections

end OAI
