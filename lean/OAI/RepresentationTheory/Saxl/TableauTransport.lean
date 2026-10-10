import OAI.RepresentationTheory.Saxl.SpechtDuality

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl
/- A change of tableau enumeration only applies a position permutation. -/
def tableauMove {n : ℕ} {μ : YoungDiagram} (s t : Tableau n μ) : Equiv.Perm (Fin n) :=
  s.trans t.symm

@[simp] lemma tableauMove_apply {n : ℕ} {μ : YoungDiagram} (s t : Tableau n μ) (i : Fin n) :
    t (tableauMove s t i) = s i := by simp [tableauMove]

@[simp] lemma tableauMove_inv_apply {n : ℕ} {μ : YoungDiagram} (s t : Tableau n μ) (i : Fin n) :
    s ((tableauMove s t)⁻¹ i) = t i := by simp [tableauMove, Equiv.Perm.inv_def]

def columnMove {n : ℕ} {μ : YoungDiagram} (s t : Tableau n μ) :
    columnGroup s ≃ columnGroup t where
  toFun h := ⟨tableauMove s t * h.val * (tableauMove s t)⁻¹, by
    intro i
    simp only [Equiv.Perm.mul_apply, tableauMove_apply]
    rw [h.property, tableauMove_inv_apply]⟩
  invFun h := ⟨(tableauMove s t)⁻¹ * h.val * tableauMove s t, by
    intro i
    simp only [Equiv.Perm.mul_apply, tableauMove_inv_apply]
    rw [h.property, tableauMove_apply]⟩
  left_inv h := by apply Subtype.ext; simp [mul_assoc]
  right_inv h := by apply Subtype.ext; simp [mul_assoc]

lemma rowWord_move {n : ℕ} {μ : YoungDiagram} (s t : Tableau n μ) :
    rowWord t = rowWord s ∘ ((tableauMove s t)⁻¹ : Equiv.Perm (Fin n)) := by
  funext i
  apply Fin.ext
  exact congrArg (fun c : μ.cells => c.val.1) (tableauMove_inv_apply s t i).symm

lemma polytabloid_move {n : ℕ} {μ : YoungDiagram} (s t : Tableau n μ) :
    polytabloid t = wordRep n (μ.colLen 0) (tableauMove s t) (polytabloid s) := by
  classical
  let := Fintype.ofFinite (columnGroup s)
  let := Fintype.ofFinite (columnGroup t)
  unfold polytabloid
  rw [map_sum]
  refine (Fintype.sum_equiv (columnMove s t).symm _ _ ?_)
  intro h
  let g := tableauMove s t
  change signC (h : Equiv.Perm (Fin n)) • wordRep n (μ.colLen 0) h.val (Pi.single (rowWord t) 1) =
    wordRep n (μ.colLen 0) g
      (signC ((columnMove s t).symm h).val •
        wordRep n (μ.colLen 0) ((columnMove s t).symm h).val (Pi.single (rowWord s) 1))
  have hs : signC ((columnMove s t).symm h).val = signC h.val := by
    change signC (g⁻¹ * h.val * g) = signC h.val
    rw [map_mul, map_mul, signC_inv]
    calc signC g * signC h.val * signC g = signC h.val * (signC g * signC g) := by ring
         _ = signC h.val := by rw [signC_mul_self, mul_one]
  rw [map_smul, hs]
  congr 1
  rw [← Module.End.mul_apply, ← map_mul]
  change wordRep n (μ.colLen 0) h.val (Pi.single (rowWord t) 1) =
    wordRep n (μ.colLen 0) (g * (g⁻¹ * h.val * g)) (Pi.single (rowWord s) 1)
  have he : g * (g⁻¹ * h.val * g) = h.val * g := by group
  have hv : wordRep n (μ.colLen 0) g (Pi.single (rowWord s) 1) = Pi.single (rowWord t) 1 := by
    rw [wordRep_single, rowWord_move s t]
  rw [he, map_mul, Module.End.mul_apply, hv]

lemma polytabloid_mem_all {n : ℕ} {μ : YoungDiagram} (s t : Tableau n μ) :
    polytabloid t ∈ spechtSub s := by
  rw [polytabloid_move s t]
  exact (spechtSub s).apply_mem_toSubmodule _ (mem_cyclic _ _)

lemma spechtSub_tableau_independent {n : ℕ} {μ : YoungDiagram} (s t : Tableau n μ) :
    spechtSub s = spechtSub t := by
  apply le_antisymm
  · exact (cyclic_le _ _ _).mpr (polytabloid_mem_all t s)
  · exact (cyclic_le _ _ _).mpr (polytabloid_mem_all s t)
end Saxl

end

end OAI
