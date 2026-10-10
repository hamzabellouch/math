import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Specht.ColumnReorder
import OAI.RepresentationTheory.UniversalSquare.Support.CommonBasis

namespace OAI

/-! Flag Columns. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl.FlagColumns
open Columns

def pure {n d : ℕ} (N : Fin n → Fin d → ℂ) : WordSpace n d :=
  fun w => ∏ i, N i (w i)

def wedge (r : ℕ) {d : ℕ} (N : ℕ → Fin d → ℂ) : WordSpace r d :=
  ∑ π : Equiv.Perm (Fin r), signC π • pure (fun i => N (π i).val)

def blocks (rs : List ℕ) {d : ℕ} (N : ℕ → Fin d → ℂ) : WordSpace rs.sum d :=
  ∑ π : Perms rs, sg π • pure (fun i => N (row (perm π (enumerate rs i))))

lemma blocks_nil {d : ℕ} (N : ℕ → Fin d → ℂ) : blocks [] N = fun _ => 1 := by
  funext w
  change (∑ π : PUnit, (1 : ℂ) • pure (n := 0) (fun i => N (row (perm (rs := []) π (enumerate [] i)))) ) w = _
  simp only [Fintype.sum_unique, one_smul]
  simp [pure]

lemma blocks_cons (r : ℕ) (rs : List ℕ) {d : ℕ} (N : ℕ → Fin d → ℂ) :
    blocks (r::rs) N = positionProduct finSumFinEquiv.symm
      (wedge r N) (blocks rs N) := by
  classical
  funext w
  change (∑ π : Perms (r::rs), sg π • pure
    (fun q => N (row (perm π (enumerate (r::rs) q))))) w =
    wedge r N (leftWord finSumFinEquiv.symm w) *
      blocks rs N (rightWord finSumFinEquiv.symm w)
  simp only [Perms, Fintype.sum_prod_type, sg, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, wedge, blocks]
  change (∑ π, ∑ σ, ((Equiv.Perm.sign π : ℤ) : ℂ) * sg σ * _) =
    (∑ π : Equiv.Perm (Fin r), ((Equiv.Perm.sign π : ℤ) : ℂ) * _) * _
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro π hπ
  apply Finset.sum_congr rfl
  intro σ hσ
  have hp : pure (fun q => N (row (perm (rs := r::rs) (π,σ) (enumerate (r::rs) q)))) w =
      pure (fun q => N (π q).val) (leftWord finSumFinEquiv.symm w) *
        pure (fun q => N (row (perm σ (enumerate rs q))))
          (rightWord finSumFinEquiv.symm w) := by
    unfold pure
    change (∏ i : Fin (r + rs.sum), N (row (perm (rs := r::rs) (π, σ)
      (enumerate (r::rs) i))) (w i)) = _
    rw [Fin.prod_univ_add]
    congr 1
    · apply Finset.prod_congr rfl
      intro i hi
      erw [enumerate_left r rs i]
      rfl
    · apply Finset.prod_congr rfl
      intro i hi
      erw [enumerate_right r rs i]
      rfl
  rw [hp]
  ring

lemma mapped_placed {rs : List ℕ} {μ : YoungDiagram} {d : ℕ}
    (e : Cells rs ≃ μ.cells)
    (hr : ∀ c, (e c).val.1 = row c)
    (hc : ∀ c c', (e c).val.2 = (e c').val.2 ↔ col c = col c')
    (N : ℕ → Fin d → ℂ) :
    wordMap (fun (i : Fin (μ.colLen 0)) a => N i.val a)
      (polytabloid ((enumerate rs).trans e)) = blocks rs N := by
  classical
  have hg : columnGroup ((enumerate rs).trans e) =
      fiberGroup (fun i : Fin rs.sum => col (enumerate rs i)) := by
    apply Subgroup.ext
    intro g
    change (∀ i, (e (enumerate rs (g i))).val.2 = (e (enumerate rs i)).val.2) ↔ _
    simp only [hc]
    rfl
  let := Fintype.ofFinite (fiberGroup (fun i : Fin rs.sum => col (enumerate rs i)))
  rw [polytabloid_eq_altWord, hg, altWord_inverse_sum, map_sum]
  unfold blocks
  symm
  apply Fintype.sum_equiv (Equiv.ofBijective (listColumnPerm rs) (listColumnPerm_bijective rs))
  intro π
  simp only [Equiv.ofBijective_apply, map_smul]
  rw [listColumnPerm_sign]
  congr 1
  funext w
  rw [wordMap_single]
  unfold pure
  apply Finset.prod_congr rfl
  intro q hq
  apply congrArg (fun i => N i (w q))
  change row (perm π (enumerate rs q)) = (e (enumerate rs ((listColumnPerm rs π).val q))).val.1
  rw [hr]
  simp only [listColumnPerm, Equiv.permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply]

def tensorList {α : Type*} (k : α → ℕ) {d : ℕ}
    (v : ∀ a, WordSpace (k a) d) : (as : List α) → WordSpace (as.map k).sum d
  | [] => fun _ => 1
  | a::as => positionProduct finSumFinEquiv.symm (v a) (tensorList k v as)

lemma blocks_pair_tensorList {α : Type*} (k : α → ℕ) {d : ℕ}
    (v : ∀ a, WordSpace (k a) d) (as : List α) (N : ℕ → Fin d → ℂ) :
    dotProduct (blocks (as.map k) N) (tensorList k v as) =
      (as.map (fun a => dotProduct (wedge (k a) N) (v a))).prod := by
  induction as with
  | nil =>
    change dotProduct (blocks [] N) (fun _ => (1 : ℂ)) = 1
    rw [blocks_nil]
    change (∑ _ : Fin 0 → Fin d, (1:ℂ) * 1) = 1
    simp
  | cons a as ih =>
    change dotProduct (blocks (k a :: as.map k) N)
      (positionProduct finSumFinEquiv.symm (v a) (tensorList k v as)) = _
    rw [blocks_cons]
    change dotProduct
      (positionProduct (n := k a + (as.map k).sum) finSumFinEquiv.symm
        (wedge (k a) N) (blocks (as.map k) N))
      (positionProduct finSumFinEquiv.symm (v a) (tensorList k v as)) = _
    rw [positionProduct_pair, ih]
    rfl

lemma altWord_injective_base {n d : ℕ} (G : Subgroup (Equiv.Perm (Fin n)))
    (a : Fin n → Fin d) (ha : Function.Injective a) : altWord G a a = 1 := by
  classical
  let := Fintype.ofFinite G
  unfold altWord
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single 1]
  · simp [wordRep]
  · intro g hg hne
    have hn : a ∘ (g : Equiv.Perm (Fin n)) ≠ a := by
      intro he
      apply hne
      apply Subtype.ext
      apply Equiv.ext
      intro i
      exact ha (congrFun he i)
    change signC g.val * (Pi.single a (1 : ℂ) : WordSpace n d)
      (a ∘ g.val) = 0
    rw [Pi.single_eq_of_ne hn, mul_zero]
  · simp

lemma altWord_real {n d : ℕ} (G : Subgroup (Equiv.Perm (Fin n)))
    (a : Fin n → Fin d) : star (altWord G a) = altWord G a := by
  classical
  let := Fintype.ofFinite G
  funext w
  simp only [altWord, Pi.star_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    star_sum, star_mul]
  apply Finset.sum_congr rfl
  intro g hg
  simp [signC, wordRep, Pi.single_apply]

lemma wedge_eq_mapped_alt {r d : ℕ} (h : r ≤ d) (N : ℕ → Fin d → ℂ) :
    wedge r N = wordMap (fun i a => N i.val a)
      (altWord (⊤ : Subgroup (Equiv.Perm (Fin r))) (Fin.castLE h)) := by
  classical
  rw [altWord_inverse_sum, map_sum]
  unfold wedge
  symm
  let := Fintype.ofFinite (⊤ : Subgroup (Equiv.Perm (Fin r)))
  let e : (⊤ : Subgroup (Equiv.Perm (Fin r))) ≃ Equiv.Perm (Fin r) :=
    { toFun := Subtype.val
      invFun := fun π => ⟨π, Subgroup.mem_top π⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  apply Fintype.sum_equiv e
  intro π
  simp only [map_smul]
  congr 1
  funext w
  rw [wordMap_single]
  rfl

theorem common_flag_tensorList {α : Type*} (k : α → ℕ) (d : ℕ)
    (v : ∀ a, WordSpace (k a) d) (as : List α)
    (hd : ∀ a ∈ as, k a ≤ d)
    (h : ∀ a ∈ as, ∃ N : ℕ → Fin d → ℂ,
      dotProduct (wedge (k a) N) (v a) ≠ 0) :
    ∃ L : Fin d → Fin d → ℂ, (Matrix.of L).det ≠ 0 ∧
      dotProduct (blocks (as.map k) (fun i a => if hi : i < d then L ⟨i,hi⟩ a else 0))
        (tensorList k v as) ≠ 0 := by
  classical
  let ι := {a // a ∈ as}
  let : Fintype ι := Fintype.ofFinite _
  let x : ∀ a : ι, WordSpace (k a.val) d := fun a =>
    altWord ⊤ (Fin.castLE (hd a.val a.property))
  have hx (a : ι) : ∃ L : Fin d → Fin d → ℂ,
      dotProduct (wordMap L (x a)) (v a.val) ≠ 0 := by
    obtain ⟨N,hN⟩ := h a.val a.property
    refine ⟨fun i j => N i.val j, ?_⟩
    rwa [← wedge_eq_mapped_alt (hd a.val a.property)]
  obtain ⟨L,hL,hp⟩ := wordMap_common_invertible (fun a : ι => k a.val) d x
    (fun a => v a.val) hx
  refine ⟨L,hL,?_⟩
  rw [blocks_pair_tensorList]
  apply List.prod_ne_zero
  intro hz
  obtain ⟨a,ha,heq⟩ := List.mem_map.mp hz
  have he : wedge (k a) (fun i b => if hi : i < d then L ⟨i,hi⟩ b else 0) =
      wordMap L (x ⟨a,ha⟩) := by
    rw [wedge_eq_mapped_alt (hd a ha)]
    have hn : (fun (i : Fin d) b => if hi : i.val < d then L ⟨i.val,hi⟩ b else 0) = L := by
      funext i b
      exact dite_eq_left i.isLt
    rw [hn]
  exact hp ⟨a,ha⟩ (he ▸ heq)

end Saxl.FlagColumns
end
end

end OAI
