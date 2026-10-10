import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Contraction.RowCertificates

namespace OAI

/-! Three Row Pieri. -/

section

noncomputable section
namespace Saxl

lemma constant_word_support {n d : ℕ} (a : Fin d) (μ : YoungDiagram)
    (t : Tableau n μ) (hμ : μ.colLen 0 ≤ 1) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep n d) (Pi.single (fun _ => a) 1)).toRepresentation, F ≠ 0 := by
  classical
  let φ : Fin (μ.colLen 0) → Fin d := fun _ => a
  have hφ : Function.Injective φ := by
    intro i j hij
    apply Fin.ext
    have hi := i.isLt
    have hj := j.isLt
    omega
  let G := (letterLift φ).comp (spechtInclusion t)
  have hG (x : Specht t) : G x ∈ cyclic (wordRep n d) (Pi.single (fun _ => a) 1) := by
    change letterLift φ x.val ∈ _
    rw [← (Pi.basisFun ℂ (Fin n → Fin (μ.colLen 0))).sum_repr x.val]
    simp only [map_sum,map_smul,Pi.basisFun_apply,letterLift_single]
    apply Submodule.sum_mem
    intro w hw
    exact Submodule.smul_mem _ _ (mem_cyclic _ _)
  let F : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep n d) (Pi.single (fun _ => a) 1)).toRepresentation := {
    toLinearMap := G.toLinearMap.codRestrict _ hG
    isIntertwining' g := by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      exact LinearMap.congr_fun (G.isIntertwining' g) x }
  refine ⟨F,?_⟩
  intro hz
  have he := congrArg (fun Q : Representation.IntertwiningMap (spechtRep t)
    (cyclic (wordRep n d) (Pi.single (fun _ => a) 1)).toRepresentation =>
      (Q ⟨polytabloid t,mem_cyclic _ _⟩).val) hz
  change letterLift φ (polytabloid t) = 0 at he
  exact polytabloid_ne_zero t ((letterLift_injective φ hφ) (he.trans (map_zero _).symm))

lemma lift_cyclic_support {n a d : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (φ : Fin a → Fin d) (hφ : Function.Injective φ) (v : WordSpace n a)
    (hs : ∃ F : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep n a) v).toRepresentation, F ≠ 0) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep n d) (letterLift φ v)).toRepresentation, F ≠ 0 := by
  obtain ⟨F,hF⟩ := hs
  refine ⟨(cyclicMap (letterLift φ) v).comp F,?_⟩
  intro hz
  apply hF
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  apply letterLift_injective φ hφ
  have he := congrArg (fun Q : Representation.IntertwiningMap (spechtRep t)
    (cyclic (wordRep n d) (letterLift φ v)).toRepresentation => (Q x).val) hz
  change letterLift φ (F x).val = 0 at he
  change letterLift φ (F x).val = letterLift φ 0
  simpa only [map_zero] using he

namespace ThreeRow

def colorTensor {n r a m s : ℕ} (q : Fin a ≃ Fin m ⊕ Fin m)
    (p : Fin r ≃ Fin a ⊕ Fin s) (e : Fin n ≃ Fin r ⊕ Fin 3) : WordSpace n 5 :=
  positionProduct e
    (positionProduct p (letterLift (Fin.castAdd 2) (symmetricPairs q 3))
      (Pi.single (fun _ => (3 : Fin 5)) 1))
    (Pi.single (fun _ => (4 : Fin 5)) 1)

theorem colorTensor_support {n r a m s : ℕ} (q : Fin a ≃ Fin m ⊕ Fin m)
    (p : Fin r ≃ Fin a ⊕ Fin s) (e : Fin n ≃ Fin r ⊕ Fin 3)
    {ν η μ : YoungDiagram} (tν : Tableau a ν) (tη : Tableau r η) (tμ : Tableau n μ)
    (hev : ∀ i, Even (ν.rowLen i)) (hν : ν.colLen 0 ≤ 3)
    (hs : HorizontalStrip ν η) (ht : HorizontalStrip η μ) :
    ∃ F : Representation.IntertwiningMap (spechtRep tμ)
      (cyclic (wordRep n 5) (colorTensor q p e)).toRepresentation, F ≠ 0 := by
  have hv : letterLift (Fin.castAdd 2) (symmetricPairs q 3) ∈
      alphabetSub a 5 (fun z => z.val < 3) := by
    apply letterLift_mem_alphabet
    intro i
    exact i.isLt
  have hu : (Pi.single (fun _ : Fin s => (3 : Fin 5)) (1 : ℂ)) ∈
      alphabetSub s 5 (fun z => ¬ z.val < 3) :=
    single_mem_alphabet _ _ (by intro i; decide)
  obtain ⟨F,hF⟩ := lift_cyclic_support tν (Fin.castAdd 2) (Fin.castAdd_injective 3 2) _
    (even_rows_symmetricPairs_support q ν tν hev hν)
  obtain ⟨G,hG⟩ := strip_product_support (SizedStripChain.of_horizontal hs) tν tη p _ _
    (fun z => z.val < 3) hv hu F hF (by
      intro ξ tξ hξ
      exact constant_word_support 3 ξ tξ hξ)
  refine strip_product_support (SizedStripChain.of_horizontal ht) tη tμ e
    (positionProduct p (letterLift (Fin.castAdd 2) (symmetricPairs q 3))
      (Pi.single (fun _ => (3 : Fin 5)) 1))
    (Pi.single (fun _ => (4 : Fin 5)) 1) (fun z => z.val < 4) ?_ ?_ G hG ?_
  · refine positionProduct_alphabet p (fun z => z.val < 4) _ _ ?_ ?_
    · apply letterLift_mem_alphabet
      intro i
      change i.val < 4
      have := i.isLt
      omega
    · exact single_mem_alphabet _ _ (by intro i; decide)
  · exact single_mem_alphabet _ _ (by intro i; decide)
  · intro ξ tξ hξ
    exact constant_word_support 4 ξ tξ hξ

end ThreeRow
end Saxl
end
end

end OAI
