import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Specht.ThreeRowTensors

namespace OAI

/-! Three Row Generator. -/

section

noncomputable section
namespace Saxl.ThreeRow

def sixPairForm : Matrix (Fin 6) (Fin 6) ℂ :=
  !![0,1,0,0,0,0; 1,0,0,0,0,0; 0,0,0,-1,0,0;
     0,0,-1,0,0,0; 0,0,0,0,0,0; 0,0,0,0,0,0]

def tripleColors : Fin 3 → Fin 6 := ![4,5,1]

def symmetricTriple : WordSpace 3 6 :=
  ∑ g : Equiv.Perm (Fin 3), Pi.single (tripleColors ∘ g) 1

def generator {n r a m s : ℕ} (q : Fin a ≃ Fin m ⊕ Fin m)
    (p : Fin r ≃ Fin a ⊕ Fin s) (e : Fin n ≃ Fin r ⊕ Fin 3) : WordSpace n 6 :=
  positionProduct e (positionProduct p (pairFormTensor q sixPairForm)
    (Pi.single (fun _ => (0 : Fin 6)) 1)) symmetricTriple

def densityMap (z : Parameters) : Fin 6 → Fin 3 → ℂ :=
  ![ (fun i => z (idx 2 i)), (fun i => z 12 * z (idx 3 i)),
     (fun i => z (idx 0 i)), (fun i => z (idx 1 i)),
     (fun i => z 12 * z (idx 3 i)), (fun i => z 12 * z (idx 3 i)) ]

lemma densityMap_triple (z : Parameters) (i : Fin 3) :
    densityMap z (tripleColors i) = fun j => z 12 * z (idx 3 j) := by
  fin_cases i <;> rfl

lemma densityMap_form (z : Parameters) :
    (fun i j => ∑ k : Fin 6 × Fin 6,
      sixPairForm k.1 k.2 * densityMap z k.1 i * densityMap z k.2 j) = gram z := by
  funext i j
  simp [Fintype.sum_prod_type,Fin.sum_univ_succ,sixPairForm,densityMap,gram]
  ring

lemma densityMap_symmetricTriple (z : Parameters) :
    wordMap (densityMap z) symmetricTriple =
      (6 * z 12^3) • powerVector 3 (fun i => z (idx 3 i)) := by
  classical
  have h (g : Equiv.Perm (Fin 3)) :
      wordMap (densityMap z) (Pi.single (tripleColors ∘ g) 1) =
        z 12^3 • powerVector 3 (fun i => z (idx 3 i)) := by
    funext w
    simp only [wordMap_single, Function.comp_apply, densityMap_triple]
    simp [powerVector, Finset.prod_mul_distrib]
  rw [symmetricTriple,map_sum]
  simp only [h,Finset.sum_const,Finset.card_univ,Fintype.card_perm,Fintype.card_fin]
  norm_num [← Nat.cast_smul_eq_nsmul ℂ,smul_smul]

lemma generator_image {n r a m s : ℕ} (q : Fin a ≃ Fin m ⊕ Fin m)
    (p : Fin r ≃ Fin a ⊕ Fin s) (e : Fin n ≃ Fin r ⊕ Fin 3) (z : Parameters) :
    wordMap (densityMap z) (generator q p e) =
      (6 * z 12^3) • independentFamily q p e (parameterMap z) := by
  rw [generator,wordMap_positionProduct,wordMap_positionProduct,wordMap_pairFormTensor,
    densityMap_form,wordMap_constant,densityMap_symmetricTriple,independentFamily,
    matrixCoord_parameter,xCoord_parameter,yCoord_parameter]
  funext w
  change _ * ((6*z 12^3) * _) = (6*z 12^3) * (_ * _)
  change (pairFormTensor q (gram z) (leftWord p (leftWord e w)) *
    powerVector s (fun i => z (idx 2 i)) (rightWord p (leftWord e w))) *
    ((6*z 12^3) * powerVector 3 (fun i => z (idx 3 i)) (rightWord e w)) = _
  dsimp [positionProduct]
  ring

theorem generator_support_of_colorTensor {n r a m s : ℕ} (q : Fin a ≃ Fin m ⊕ Fin m)
    (p : Fin r ≃ Fin a ⊕ Fin s) (e : Fin n ≃ Fin r ⊕ Fin 3)
    {μ : YoungDiagram} (t : Tableau n μ) (ht : μ.colLen 0 ≤ 3)
    (hs : ∃ F : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep n 5) (colorTensor q p e)).toRepresentation, F ≠ 0) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep n 6) (generator q p e)).toRepresentation, F ≠ 0 := by
  obtain ⟨g,w,hw⟩ := independent_nonvanishing q p e t ht hs
  let x := letterLift (Fin.castLE ht) (wordRep n (μ.colLen 0) g (polytabloid t))
  have hex : ∃ z : Parameters, z 12 ≠ 0 ∧
      dotProduct x (independentFamily q p e (parameterMap z)) ≠ 0 := by
    by_contra! hn
    exact hw (joint_density _ (independentFamily_analytic q p e x) hn w)
  obtain ⟨z,hz,hpair⟩ := hex
  have hnonzero : dotProduct x (wordMap (densityMap z) (generator q p e)) ≠ 0 := by
    rw [generator_image,dotProduct_smul]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hz)) hpair
  rw [← wordMap_pair_transpose] at hnonzero
  change dotProduct (wordMap _ (letterLift (Fin.castLE ht)
    (wordRep n (μ.colLen 0) g (polytabloid t)))) (generator q p e) ≠ 0 at hnonzero
  rw [wordMap_letterLift] at hnonzero
  exact (dual_polytabloid_iff t _).mpr ⟨g,_,hnonzero⟩

theorem generator_support {n r a m s : ℕ} (q : Fin a ≃ Fin m ⊕ Fin m)
    (p : Fin r ≃ Fin a ⊕ Fin s) (e : Fin n ≃ Fin r ⊕ Fin 3)
    {ν η μ : YoungDiagram} (tν : Tableau a ν) (tη : Tableau r η) (tμ : Tableau n μ)
    (hev : ∀ i, Even (ν.rowLen i)) (hν : ν.colLen 0 ≤ 3) (hμ : μ.colLen 0 ≤ 3)
    (hs : HorizontalStrip ν η) (ht : HorizontalStrip η μ) :
    ∃ F : Representation.IntertwiningMap (spechtRep tμ)
      (cyclic (wordRep n 6) (generator q p e)).toRepresentation, F ≠ 0 :=
  generator_support_of_colorTensor q p e tμ hμ
    (colorTensor_support q p e tν tη tμ hev hν hs ht)

end Saxl.ThreeRow
end
end

end OAI
