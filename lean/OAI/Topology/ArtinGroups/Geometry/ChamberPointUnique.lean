import Mathlib
import OAI.Topology.ArtinGroups.Geometry.ChamberPoint

namespace OAI

namespace HarmonicArtin.Geometric
open CoxeterExchange _root_.Matrix _root_.OAI.Matrix
open scoped BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type*} [Fintype S] [DecidableEq S] (M : CoxeterMatrix S) [Finite M.Group]

lemma chamberPoint_unique (p : S → ℝ) (hp : cartan M *ᵥ p=1) : p=chamberPoint M := by
  let := Fintype.ofFinite M.Group
  apply (Matrix.mulVec_injective_iff_isUnit.mpr (cartan_posDef M.toCoxeterSystem).isUnit)
  exact hp.trans (chamberPoint_spec M).symm

lemma chamberPoint_component (R : Set S) [Finite (restrictedMatrix M R).Group]
    (hR : ∀ i ∈ R, ∀ j ∉ R,cartan M i j=0) :
    (fun i : R => chamberPoint M i)=chamberPoint (restrictedMatrix M R) := by
  apply chamberPoint_unique
  ext i
  have hh := congrFun (chamberPoint_spec M) (i:S)
  change ∑ j,cartan (restrictedMatrix M R) i j * chamberPoint M j=1
  change ∑ j,cartan M i j * chamberPoint M j=1 at hh
  rw [cartan_restricted]
  simp only [Matrix.submatrix_apply]
  rw [←hh]
  symm
  apply Finset.sum_congr_set R
  · intro j hj; rfl
  · intro j hj
    rw [hR i i.property j hj,zero_mul]

omit [Fintype S] [Finite M.Group] in
lemma cartan_cross_two (i j : S) (h : M i j=2) : cartan M i j=0 := by
  have hn : i≠j := by intro he; subst j; simp at h
  simp [cartan,hn,h,Real.cos_pi_div_two]

lemma chamberPoint_diagram_component (R : Set S) [Finite (restrictedMatrix M R).Group]
    (hR : ∀ i ∈ R,∀ j ∉ R,M i j=2) :
    (fun i : R => chamberPoint M i)=chamberPoint (restrictedMatrix M R) :=
  chamberPoint_component M R (fun i hi j hj => cartan_cross_two M i j (hR i hi j hj))

lemma finite_average_product {A B E F : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] (f : A → E) (g : B → F) :
    (Fintype.card (A × B) : ℝ)⁻¹ • (∑ p : A × B,(f p.1,g p.2)) =
      ((Fintype.card A : ℝ)⁻¹ • ∑ a,f a,(Fintype.card B : ℝ)⁻¹ • ∑ b,g b) := by
  have hA : (Fintype.card A : ℝ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hB : (Fintype.card B : ℝ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  apply Prod.ext
  · simp only [Prod.smul_fst,Prod.fst_sum,Fintype.card_prod,Nat.cast_mul,Fintype.sum_prod_type,
      Finset.sum_const,Finset.card_univ]
    simp only [← Nat.cast_smul_eq_nsmul ℝ,←Finset.smul_sum,smul_smul]
    congr 1
    field_simp
  · simp only [Prod.smul_snd,Prod.snd_sum,Fintype.card_prod,Nat.cast_mul,Fintype.sum_prod_type,
      Finset.sum_const,Finset.card_univ]
    simp only [← Nat.cast_smul_eq_nsmul ℝ,smul_smul]
    congr 1
    field_simp

end HarmonicArtin.Geometric

end OAI
