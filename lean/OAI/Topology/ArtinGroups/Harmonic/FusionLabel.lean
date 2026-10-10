import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.QuantumNumber

namespace OAI

namespace HarmonicArtin

variable {E : Type*} [Fintype E] [DecidableEq E] (m : E → ℕ)

abbrev FusionLabel := (e : E) → StringLabel (m e)

noncomputable def fusionWeight (L : FusionLabel m) : ℝ :=
  ∏ e, stringWeight (m e) (L e)

omit [DecidableEq E] in
lemma fusionWeight_pos (hm : ∀ e, 2 ≤ m e) (L : FusionLabel m) :
    0 < fusionWeight m L := by
  apply Finset.prod_pos
  intro e _
  exact stringWeight_pos (hm e) (L e)

noncomputable def factorMultiplicity (e : E) (L L' : FusionLabel m) : ℕ :=
  if ∀ f, f ≠ e → L f = L' f then stringMultiplicity (m e) (L e) (L' e) else 0

lemma factorMultiplicity_symm (e : E) (L L' : FusionLabel m) :
    factorMultiplicity m e L L' = factorMultiplicity m e L' L := by
  unfold factorMultiplicity
  have hh : (∀ f, f ≠ e → L f = L' f) ↔ (∀ f, f ≠ e → L' f = L f) := by
    constructor <;> intro h f hf <;> exact (h f hf).symm
  simp only [hh, stringMultiplicity_symm]

lemma factorMultiplicity_le_one (e : E) (L L' : FusionLabel m) :
    factorMultiplicity m e L L' ≤ 1 := by
  unfold factorMultiplicity
  split_ifs
  · exact stringMultiplicity_le_one _ _ _
  · omega

lemma fusionWeight_update (L : FusionLabel m) (e : E) (j : StringLabel (m e)) :
    fusionWeight m (Function.update L e j) =
      stringWeight (m e) j * ∏ f ∈ Finset.univ.erase e, stringWeight (m f) (L f) := by
  unfold fusionWeight
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ e)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro f hf
  rw [Function.update_of_ne (Finset.mem_erase.mp hf).1]

lemma factorMultiplicity_update (L : FusionLabel m) (e : E) (j : StringLabel (m e)) :
    factorMultiplicity m e L (Function.update L e j) =
      stringMultiplicity (m e) (L e) j := by
  unfold factorMultiplicity
  have hh : ∀ f, f ≠ e → L f = Function.update L e j f := by
    intro f hf
    rw [Function.update_of_ne hf]
  rw [ite_eq_left hh, Function.update_self]

lemma factor_dimension_identity (hm : ∀ e, 2 ≤ m e) (e : E) (L : FusionLabel m) :
    (∑ L' : FusionLabel m, (factorMultiplicity m e L L' : ℝ) * fusionWeight m L') =
      (2 * Real.cos (Real.pi / m e)) * fusionWeight m L := by
  classical
  have hx : Function.Injective (Function.update L e) := by
    intro i j h
    have hh := congrFun h e
    simpa only [Function.update_self] using hh
  have hs : (∑ j : StringLabel (m e),
      (stringMultiplicity (m e) (L e) j : ℝ) * fusionWeight m (Function.update L e j)) =
      ∑ L' : FusionLabel m, (factorMultiplicity m e L L' : ℝ) * fusionWeight m L' := by
    apply Fintype.sum_of_injective (Function.update L e) hx
    · intro L' hL'
      have hh : ¬ ∀ f, f ≠ e → L f = L' f := by
        intro hh
        apply hL'
        refine ⟨L' e, ?_⟩
        funext f
        by_cases hf : f=e
        · subst f; exact Function.update_self _ _ _
        · rw [Function.update_of_ne hf]
          exact hh f hf
      simp only [factorMultiplicity, ite_eq_right hh, Nat.cast_zero, zero_mul]
    · intro j
      rw [factorMultiplicity_update]
  rw [← hs]
  simp_rw [fusionWeight_update, ← mul_assoc]
  rw [← Finset.sum_mul, string_dimension_identity (hm e)]
  rw [fusionWeight, ← Finset.mul_prod_erase _ _ (Finset.mem_univ e)]
  ring

inductive FusionEdge (E : Type*)
  | units : ℕ → FusionEdge E
  | string : E → FusionEdge E

noncomputable def FusionEdge.multiplicity (d : FusionEdge E) (L L' : FusionLabel m) : ℕ :=
  match d with
  | .units n => if L = L' then n else 0
  | .string e => factorMultiplicity m e L L'

noncomputable def FusionEdge.dimension (d : FusionEdge E) : ℝ :=
  match d with
  | .units n => n
  | .string e => 2 * Real.cos (Real.pi / m e)

lemma FusionEdge.multiplicity_symm (d : FusionEdge E) (L L' : FusionLabel m) :
    d.multiplicity m L L' = d.multiplicity m L' L := by
  cases d with
  | units n => simp only [multiplicity, eq_comm]
  | string e => exact factorMultiplicity_symm m e L L'

lemma FusionEdge.dimension_identity (hm : ∀ e, 2 ≤ m e) (d : FusionEdge E)
    (L : FusionLabel m) :
    (∑ L', (d.multiplicity m L L' : ℝ) * fusionWeight m L') =
      d.dimension m * fusionWeight m L := by
  classical
  cases d with
  | units n =>
    simp only [multiplicity, Nat.cast_ite, Nat.cast_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true, dimension]
  | string e => exact factor_dimension_identity m hm e L

end HarmonicArtin

end OAI
