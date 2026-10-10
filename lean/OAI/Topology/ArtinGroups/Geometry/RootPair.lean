import Mathlib
import OAI.Topology.ArtinGroups.Geometry.RootNonnegAscent

namespace OAI

namespace HarmonicArtin.Geometric
open Matrix HarmonicArtin.CoxeterExchange
open scoped BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S W : Type*} [Fintype S] [DecidableEq S] [Group W]
  {M : CoxeterMatrix S} (cs : CoxeterSystem M W)

noncomputable def rootPair (M : CoxeterMatrix S) (x y : S → ℝ) : ℝ :=
  x ⬝ᵥ (cartan M *ᵥ y)

lemma rootPair_symm (M : CoxeterMatrix S) (x y : S → ℝ) : rootPair M x y=rootPair M y x := by
  simp only [rootPair,Matrix.mulVec,dotProduct,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [cartan_symm M j i]
  ring

lemma rootPair_sub_left (M : CoxeterMatrix S) (x y z : S → ℝ) :
    rootPair M (x-y) z=rootPair M x z-rootPair M y z := by
  simp only [rootPair,sub_dotProduct]

lemma rootPair_sub_right (M : CoxeterMatrix S) (x y z : S → ℝ) :
    rootPair M x (y-z)=rootPair M x y-rootPair M x z := by
  simp only [rootPair,Matrix.mulVec_sub,dotProduct_sub]

lemma rootPair_smul_left (M : CoxeterMatrix S) (r : ℝ) (x y : S → ℝ) :
    rootPair M (r • x) y=r*rootPair M x y := by
  simp only [rootPair,smul_dotProduct,smul_eq_mul]

lemma rootPair_smul_right (M : CoxeterMatrix S) (r : ℝ) (x y : S → ℝ) :
    rootPair M x (r • y)=r*rootPair M x y := by
  rw [rootPair_symm,rootPair_smul_left,rootPair_symm M y x]

lemma rootPair_basis_left (M : CoxeterMatrix S) (i : S) (x : S → ℝ) :
    rootPair M (Pi.single i 1) x=rootRow M i x := by
  simp [rootPair,dotProduct,Pi.single_apply,rootRow_apply]

lemma rootPair_basis_right (M : CoxeterMatrix S) (i : S) (x : S → ℝ) :
    rootPair M x (Pi.single i 1)=rootRow M i x := by
  rw [rootPair_symm,rootPair_basis_left]

lemma reflection_rootPair (M : CoxeterMatrix S) (i : S) (x y : S → ℝ) :
    rootPair M (simpleReflection M i x) (simpleReflection M i y)=rootPair M x y := by
  simp only [simpleReflection_apply,← rootRow_apply,rootPair_sub_left,rootPair_sub_right,
    rootPair_smul_left,rootPair_smul_right,rootPair_basis_left,rootPair_basis_right,
    map_sub,map_smul,rootRow_single,cartan_diag,smul_eq_mul]
  ring

lemma representation_rootPair (w : W) (x y : S → ℝ) :
    rootPair M (representation cs w x) (representation cs w y)=rootPair M x y := by
  induction w using cs.simple_induction_left generalizing x y with
  | one => simp
  | mul_simple_left w i ih =>
    rw [map_mul,LinearEquiv.mul_apply,LinearEquiv.mul_apply,representation_simple,
      reflection_rootPair,ih]

lemma rootRow_representation (w : W) (s : S) (p : S → ℝ) :
    rootRow M s (representation cs w p)=rootPair M (representation cs w⁻¹ (Pi.single s 1)) p := by
  have h := representation_rootPair cs w (representation cs w⁻¹ (Pi.single s 1)) p
  rw [← LinearEquiv.mul_apply,← map_mul,mul_inv_cancel,map_one] at h
  change rootPair M (Pi.single s 1) (representation cs w p)=_ at h
  simpa only [rootPair_basis_left] using h

lemma rootPair_pos (M : CoxeterMatrix S) (p x : S → ℝ)
    (hp : ∀ i,0 < rootRow M i p) (hx : ∀ i,0 ≤ x i) (hne : x≠0) :
    0 < rootPair M x p := by
  obtain ⟨i,hi⟩ : ∃ i,x i≠0 := by
    by_contra! h
    exact hne (funext h)
  have hi' : 0 < x i := lt_of_le_of_ne (hx i) (Ne.symm hi)
  change 0 < ∑ j,x j*rootRow M j p
  exact Finset.sum_pos' (fun j _ => mul_nonneg (hx j) (hp j).le)
    ⟨i,Finset.mem_univ _,mul_pos hi' (hp i)⟩

lemma rootPair_nonpos (M : CoxeterMatrix S) (p x : S → ℝ)
    (hp : ∀ i,0 < rootRow M i p) (hx : ∀ i,x i≤0) : rootPair M x p≤0 := by
  change (∑ j,x j*rootRow M j p)≤0
  exact Finset.sum_nonpos (fun j _ => mul_nonpos_of_nonpos_of_nonneg (hx j) (hp j).le)

omit [Fintype S] [DecidableEq S] in
lemma inverse_right_length (w : W) (s : S) :
    cs.length (w⁻¹*cs.simple s)=cs.length (cs.simple s*w) := by
  rw [← cs.length_inv (cs.simple s*w),_root_.mul_inv_rev,cs.inv_simple]

theorem rootRow_pos_iff_left_ascent (p : S → ℝ) (hp : ∀ i,0 < rootRow M i p)
    (w : W) (s : S) :
    0 < rootRow M s (representation cs w p) ↔
      cs.length (cs.simple s*w)=cs.length w+1 := by
  rw [rootRow_representation]
  constructor
  · intro h
    rcases cs.length_mul_simple w⁻¹ s with ha | hd
    · simpa only [inverse_right_length,cs.length_inv] using ha
    · have hn := root_nonpos_of_descent cs w⁻¹ s hd
      exact (not_lt_of_ge (rootPair_nonpos M p _ hp hn) h).elim
  · intro h
    have ha : cs.length (w⁻¹*cs.simple s)=cs.length w⁻¹+1 := by
      simpa only [inverse_right_length,cs.length_inv] using h
    exact rootPair_pos M p _ hp (root_nonneg_of_ascent cs w⁻¹ s ha)
      (geometric_root_ne_zero cs w⁻¹ s)

theorem chamber_stabilizer (p : S → ℝ) (hp : ∀ i,0 < rootRow M i p)
    (w : W) (hw : representation cs w p=p) : w=1 := by
  by_contra h
  obtain ⟨s,hs⟩ := exists_right_descent cs (inv_ne_one.mpr h)
  have has : cs.length (cs.simple s*w)=cs.length w+1 :=
    (rootRow_pos_iff_left_ascent cs p hp w s).mp (by rw [hw]; exact hp s)
  rw [inverse_right_length,cs.length_inv] at hs
  omega

end HarmonicArtin.Geometric

end OAI
