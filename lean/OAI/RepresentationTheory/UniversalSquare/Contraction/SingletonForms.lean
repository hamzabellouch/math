import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Contraction.PairForms
import OAI.RepresentationTheory.UniversalSquare.Support.SingletonPairs

namespace OAI

/-! Singleton Forms. -/

section

noncomputable section
namespace Saxl

def singleWord {d : ℕ} (v : Fin d → ℂ) : WordSpace 1 d := fun w => v (w 0)

lemma wordMap_singleWord {a b : ℕ} (L : Fin a → Fin b → ℂ) (v : Fin a → ℂ) :
    wordMap L (singleWord v) = singleWord (fun j => ∑ i, v i * L i j) := by
  classical
  funext w
  change (∑ c : Fin 1 → Fin a, v (c 0) * ∏ i, L (c i) (w i)) = _
  simpa only [Fintype.prod_unique, show (default : Fin 1) = 0 from rfl, singleWord] using
    (Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin a))
      (fun c => v (c 0) * L (c 0) (w 0))
      (fun i => v i * L i (w 0)) (fun _ => rfl))

def pairSingletonTensor {n a m d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin 1)
    (p : Fin a ≃ Fin m ⊕ Fin m) (B : Matrix (Fin d) (Fin d) ℂ) (v : Fin d → ℂ) :
    WordSpace n d := positionProduct e (pairFormTensor p B) (singleWord v)

lemma wordMap_pairSingletonTensor {n a m d D : ℕ}
    (e : Fin n ≃ Fin a ⊕ Fin 1) (p : Fin a ≃ Fin m ⊕ Fin m)
    (L : Fin d → Fin D → ℂ) (B : Matrix (Fin d) (Fin d) ℂ) (v : Fin d → ℂ) :
    wordMap L (pairSingletonTensor e p B v) = pairSingletonTensor e p
      (fun j k => ∑ q : Fin d × Fin d, B q.1 q.2 * L q.1 j * L q.2 k)
      (fun j => ∑ i, v i * L i j) := by
  rw [pairSingletonTensor, wordMap_positionProduct, wordMap_pairFormTensor,
    wordMap_singleWord]
  rfl

def pairSingletonEquiv {n a m : ℕ} (e : Fin n ≃ Fin a ⊕ Fin 1)
    (p : Fin a ≃ Fin m ⊕ Fin m) : Fin n ≃ Fin (m+1) ⊕ Fin m :=
  e.trans ((Equiv.sumCongr p (Equiv.refl _)).trans
    ((Equiv.sumAssoc _ _ _).trans ((Equiv.sumCongr (Equiv.refl _)
      (Equiv.sumComm _ _)).trans ((Equiv.sumAssoc _ _ _).symm.trans
        (Equiv.sumCongr finSumFinEquiv (Equiv.refl _))))))

@[simp] lemma pairSingletonEquiv_left {n a m : ℕ}
    (e : Fin n ≃ Fin a ⊕ Fin 1) (p : Fin a ≃ Fin m ⊕ Fin m) (k : Fin m) :
    (pairSingletonEquiv e p).symm (Sum.inl k.castSucc) =
      e.symm (Sum.inl (p.symm (Sum.inl k))) := by
  change (pairSingletonEquiv e p).symm (Sum.inl (Fin.castAdd 1 k)) = _
  simp [pairSingletonEquiv]

@[simp] lemma pairSingletonEquiv_right {n a m : ℕ}
    (e : Fin n ≃ Fin a ⊕ Fin 1) (p : Fin a ≃ Fin m ⊕ Fin m) (k : Fin m) :
    (pairSingletonEquiv e p).symm (Sum.inr k) =
      e.symm (Sum.inl (p.symm (Sum.inr k))) := by
  simp [pairSingletonEquiv]

@[simp] lemma pairSingletonEquiv_last {n a m : ℕ}
    (e : Fin n ≃ Fin a ⊕ Fin 1) (p : Fin a ≃ Fin m ⊕ Fin m) :
    (pairSingletonEquiv e p).symm (Sum.inl (Fin.last m)) = e.symm (Sum.inr 0) := by
  have hh : Fin.last m = Fin.natAdd m (0 : Fin 1) := Fin.ext (by simp)
  rw [hh]
  simp [pairSingletonEquiv]

lemma pairSingletonTensor_one {n a m d : ℕ}
    (e : Fin n ≃ Fin a ⊕ Fin 1) (p : Fin a ≃ Fin m ⊕ Fin m) (v : Fin d → ℂ) :
    pairSingletonTensor e p (1 : Matrix (Fin d) (Fin d) ℂ) v =
      symmetricPartialPairs (pairSingletonEquiv e p) Fin.castSuccEmb v := by
  classical
  funext w
  have ht : leftWord (pairSingletonEquiv e p) w ∘ Fin.castSuccEmb =
      leftWord p (leftWord e w) := by
    funext k
    simp [leftWord]
  have hb : rightWord (pairSingletonEquiv e p) w = rightWord p (leftWord e w) := by
    funext k
    simp [rightWord,leftWord]
  have hlast : Fin.last m ∉ Set.range (Fin.castSuccEmb : Fin m ↪ Fin (m+1)) := by
    rintro ⟨k,hk⟩
    have hh := congrArg Fin.val hk
    have hh' := k.isLt
    change k.val = m at hh
    omega
  have hcast (k : Fin m) : k.castSucc ∈ Set.range (Fin.castSuccEmb : Fin m ↪ Fin (m+1)) :=
    ⟨k,rfl⟩
  have hprod : (∏ k ∈ Finset.univ.filter
        (fun k => k ∉ Set.range (Fin.castSuccEmb : Fin m ↪ Fin (m+1))),
        v (leftWord (pairSingletonEquiv e p) w k)) = v (rightWord e w 0) := by
    rw [Finset.prod_filter, Fin.prod_univ_castSucc]
    simp [leftWord,rightWord]
  unfold symmetricPartialPairs
  rw [ht,hb,hprod]
  unfold pairSingletonTensor
  rw [pairFormTensor_one]
  change (if leftWord p (leftWord e w) = rightWord p (leftWord e w) then 1 else 0) *
    v (rightWord e w 0) = _
  split_ifs <;> simp

lemma pairSingletonTensor_smul {n a m d : ℕ}
    (e : Fin n ≃ Fin a ⊕ Fin 1) (p : Fin a ≃ Fin m ⊕ Fin m)
    (B : Matrix (Fin d) (Fin d) ℂ) (v : Fin d → ℂ) (c : ℂ) :
    pairSingletonTensor e p (c • B) v = c^m • pairSingletonTensor e p B v := by
  unfold pairSingletonTensor
  rw [pairFormTensor_smul]
  funext w
  change c^m * pairFormTensor p B (leftWord e w) * singleWord v (rightWord e w) = _
  exact mul_assoc _ _ _

theorem one_odd_row_pairSingleton_support {n a m d D : ℕ}
    (e : Fin n ≃ Fin a ⊕ Fin 1) (p : Fin a ≃ Fin m ⊕ Fin m)
    (B : Matrix (Fin d) (Fin d) ℂ) (v : Fin d → ℂ)
    (L : Fin d → Fin D → ℂ) (c : ℂ) (hc : c ≠ 0)
    (hL : (fun j k => ∑ q : Fin d × Fin d, B q.1 q.2 * L q.1 j * L q.2 k) =
      c • (1 : Matrix (Fin D) (Fin D) ℂ))
    (hv : (fun j => ∑ i, v i * L i j) ≠ 0)
    (μ : YoungDiagram) (t : Tableau n μ)
    (k : ℕ) (hk : Odd (μ.rowLen k)) (he : ∀ l, l ≠ k → Even (μ.rowLen l))
    (hd : μ.colLen 0 ≤ D) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep n d) (pairSingletonTensor e p B v)).toRepresentation, F ≠ 0 := by
  let v' := fun j => ∑ i, v i * L i j
  have hmap : wordMap L (pairSingletonTensor e p B v) =
      c^m • symmetricPartialPairs (pairSingletonEquiv e p) Fin.castSuccEmb v' := by
    rw [wordMap_pairSingletonTensor, hL, pairSingletonTensor_smul, pairSingletonTensor_one]
  have hcyc : cyclic (wordRep n D) (wordMap L (pairSingletonTensor e p B v)) =
      cyclic (wordRep n D) (symmetricPartialPairs (pairSingletonEquiv e p) Fin.castSuccEmb v') := by
    rw [hmap, cyclic_smul_eq _ _ _ (pow_ne_zero m hc)]
  have hs := one_odd_row_symmetricPartialPairs_support (pairSingletonEquiv e p) Fin.castSuccEmb
    v' hv μ t k hk he hd
  rw [← hcyc] at hs
  obtain ⟨F,hF⟩ := hs
  exact cyclic_projection_support (wordMap L) (pairSingletonTensor e p B v) F hF

lemma shortPair_singleton_nonzero :
    (fun j => ∑ i : Fin 4, (Pi.single 0 (1 : ℂ) : Fin 4 → ℂ) i * shortPairCongruence i j) ≠ 0 := by
  intro h
  have hh := congrFun h (0 : Fin 4)
  norm_num [shortPairCongruence, Pi.single_apply, Fin.sum_univ_succ] at hh

theorem one_odd_row_shortPair_support {n a m : ℕ}
    (e : Fin n ≃ Fin a ⊕ Fin 1) (p : Fin a ≃ Fin m ⊕ Fin m)
    (μ : YoungDiagram) (t : Tableau n μ)
    (k : ℕ) (hk : Odd (μ.rowLen k)) (he : ∀ l, l ≠ k → Even (μ.rowLen l))
    (hd : μ.colLen 0 ≤ 4) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep n 4) (pairSingletonTensor e p shortPairForm (Pi.single 0 1))).toRepresentation,
      F ≠ 0 :=
  one_odd_row_pairSingleton_support e p shortPairForm (Pi.single 0 1)
    shortPairCongruence 2 (by norm_num) shortPairCongruence_gram
      shortPair_singleton_nonzero μ t k hk he hd

end Saxl
end
end

end OAI
