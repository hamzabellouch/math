import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Contraction.RowCertificates

namespace OAI

/-! Counted Pieri. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

theorem placed_strip_restriction_counts {n a b : ℕ} {ν μ : YoungDiagram} {bs : List ℕ}
    (hs : SizedStripChain bs ν μ) (s : Tableau a ν) (t : Tableau n μ)
    (e : Fin n ≃ Fin a ⊕ Fin b) :
    ∃ (c : Fin b → Fin bs.length) (F : Specht t →ₗ[ℂ] Specht s), Function.Surjective F ∧
      (∀ j, wordContent c j = bs.get j) ∧
      ∀ (h : Equiv.Perm (Fin a)) (q : Equiv.Perm (Fin b)), c ∘ q = c →
        ∀ x, F (spechtRep t (sumPerm e h q) x) = spechtRep s h (F x) := by
  classical
  obtain ⟨c,F,hF,hcb,hcz,hcount,hFe⟩ := stripChain_restriction_any hs s t
  let i := tableauInclusion s t hs.le
  let l : Fin a → Fin n := fun j => e.symm (Sum.inl j)
  obtain ⟨p,hp⟩ := Equiv.Perm.exists_extending_pair l i
    (fun x y h => Sum.inl.inj (e.symm.injective h)) i.injective
  have hcL (j : Fin a) : c (p (e.symm (Sum.inl j))) = 0 := by
    rw [show p (e.symm (Sum.inl j)) = i j from hp j]
    exact (hcz _).mpr ⟨j,rfl⟩
  have hcRpos (j : Fin b) : 0 < c (p (e.symm (Sum.inr j))) := by
    by_contra hn
    have hz : c (p (e.symm (Sum.inr j))) = 0 := by omega
    obtain ⟨k,hk⟩ := (hcz _).mp hz
    have hh : e.symm (Sum.inl k) = e.symm (Sum.inr j) := p.injective ((hp k).trans hk)
    have := e.symm.injective hh
    cases this
  let cb : Fin b → Fin bs.length := fun j => ⟨c (p (e.symm (Sum.inr j)))-1, by
    have := hcRpos j
    have := hcb (p (e.symm (Sum.inr j)))
    omega⟩
  have hcR (j : Fin b) : c (p (e.symm (Sum.inr j))) = (cb j).val+1 := by
    have := hcRpos j
    change _ = (c (p (e.symm (Sum.inr j)))-1)+1
    omega
  let F' := F.comp (spechtRep t p)
  have hP : Function.Surjective (spechtRep t p) := by
    intro x
    refine ⟨spechtRep t p⁻¹ x, ?_⟩
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  refine ⟨cb,F',hF.comp hP, ?_, ?_⟩
  · intro j
    change wordContent cb j = bs[j.val]
    rw [← hcount j.val j.isLt]
    unfold wordContent
    apply Finset.card_bij (fun k _ => p (e.symm (Sum.inr k)))
    · intro k hk
      simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hk ⊢
      rw [hcR,hk]
    · intro k hk l hl he
      exact Sum.inr.inj (e.symm.injective (p.injective he))
    · intro z hz
      have hcpos : c z = j.val+1 := (Finset.mem_filter.mp hz).2
      obtain ⟨w,rfl⟩ := p.surjective z
      obtain ⟨w,rfl⟩ := e.symm.surjective w
      cases w with
      | inl i => rw [hcL] at hcpos; omega
      | inr k =>
        refine ⟨k,Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩,rfl⟩
        apply Fin.ext
        rw [hcR] at hcpos
        omega
  intro h q hq x
  let g := p * sumPerm e h q * p⁻¹
  have hgL (j : Fin a) : g (p (e.symm (Sum.inl j))) = p (e.symm (Sum.inl (h j))) := by
    simp [g]
  have hgR (j : Fin b) : g (p (e.symm (Sum.inr j))) = p (e.symm (Sum.inr (q j))) := by
    simp [g]
  have hgc (j : Fin n) : c (g j) = c j := by
    obtain ⟨z,rfl⟩ := p.surjective j
    obtain ⟨z,rfl⟩ := e.symm.surjective z
    cases z with
    | inl j => rw [hgL,hcL,hcL]
    | inr j =>
      rw [hgR,hcR,hcR]
      exact congrArg (fun x : Fin bs.length => x.val+1) (congrFun hq j)
  have hgi (j : Fin a) : g (i j) = i (h j) := by rw [← hp j,← hp (h j)]; exact hgL j
  change F (spechtRep t p (spechtRep t (sumPerm e h q) x)) = spechtRep s h (F (spechtRep t p x))
  have hmul : p * sumPerm e h q = g * p := by simp [g,mul_assoc]
  rw [← Module.End.mul_apply, ← map_mul, hmul, map_mul, Module.End.mul_apply]
  exact hFe g h hgc hgi _

def orbitTensorEval {b k : ℕ} {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
    (c : Fin b → Fin k) :
    Y ⊗[ℂ] (cyclic (wordRep b k) (Pi.single c 1)).toSubmodule →ₗ[ℂ]
      ((Fin b → Fin k) → Y) :=
  (TensorProduct.piScalarRight ℂ ℂ Y (Fin b → Fin k)).toLinearMap.comp
    (TensorProduct.map LinearMap.id
      (subrepInclusion (cyclic (wordRep b k) (Pi.single c 1))).toLinearMap)

lemma orbitTensorEval_injective {b k : ℕ} {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
    (c : Fin b → Fin k) : Function.Injective (orbitTensorEval (Y := Y) c) :=
  (TensorProduct.piScalarRight ℂ ℂ Y (Fin b → Fin k)).injective.comp
    (TensorProduct.map_injective_of_flat_flat _ _ Function.injective_id Subtype.val_injective)

@[simp] lemma orbitTensorEval_tmul {b k : ℕ} {Y : Type*}
    [AddCommGroup Y] [Module ℂ Y] (c : Fin b → Fin k) (y : Y)
    (z : (cyclic (wordRep b k) (Pi.single c 1)).toSubmodule) (w : Fin b → Fin k) :
    orbitTensorEval c (y ⊗ₜ[ℂ] z) w = z.val w • y := by
  simp only [orbitTensorEval,LinearMap.comp_apply,TensorProduct.map_tmul,
    LinearMap.id_apply]
  rfl

lemma orbitTensorEval_outer {a b k : ℕ} {Y : Type*}
    [AddCommGroup Y] [Module ℂ Y]
    (τ : Representation ℂ (Equiv.Perm (Fin a)) Y) (c : Fin b → Fin k)
    (g : Equiv.Perm (Fin a) × Equiv.Perm (Fin b))
    (x : Y ⊗[ℂ] (cyclic (wordRep b k) (Pi.single c 1)).toSubmodule)
    (w : Fin b → Fin k) :
    orbitTensorEval c (outer τ (cyclic (wordRep b k) (Pi.single c 1)).toRepresentation g x) w =
      τ g.1 (orbitTensorEval c x (w ∘ g.2)) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add,Pi.add_apply,hx,hy]
  | tmul y z =>
    change orbitTensorEval c (τ g.1 y ⊗ₜ[ℂ]
      (cyclic (wordRep b k) (Pi.single c 1)).toRepresentation g.2 z) w = _
    simp only [orbitTensorEval_tmul,map_smul]
    rfl

def orbitTensorMap {n a b k : ℕ} {X Y : Type*}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (e : Fin n ≃ Fin a ⊕ Fin b) (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    (c : Fin b → Fin k) (F : X →ₗ[ℂ] Y) :
    X →ₗ[ℂ] Y ⊗[ℂ] (cyclic (wordRep b k) (Pi.single c 1)).toSubmodule :=
  ∑ q : Equiv.Perm (Fin b),
    ((TensorProduct.mk ℂ Y (cyclic (wordRep b k) (Pi.single c 1)).toSubmodule).flip
      ((cyclic (wordRep b k) (Pi.single c 1)).toRepresentation q ⟨Pi.single c 1,mem_cyclic _ _⟩)).comp
        (F.comp (ρ (sumPerm e 1 q⁻¹)))

lemma orbitTensorMap_eval {n a b k : ℕ} {X Y : Type*}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (e : Fin n ≃ Fin a ⊕ Fin b) (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    (c : Fin b → Fin k) (F : X →ₗ[ℂ] Y) (x : X) :
    orbitTensorEval c (orbitTensorMap e ρ c F x) = bandOrbitMap e ρ c F x := by
  ext w
  simp only [orbitTensorMap,LinearMap.sum_apply,LinearMap.comp_apply,
    LinearMap.flip_apply,TensorProduct.mk_apply,map_sum,Finset.sum_apply,
    orbitTensorEval_tmul]
  change (∑ q : Equiv.Perm (Fin b), (wordRep b k q (Pi.single c 1)) w • _) = _
  simp only [wordRep_single]
  rfl

theorem stripChain_outer_map {n a b : ℕ} {ν μ : YoungDiagram} {bs : List ℕ}
    {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
    (hs : SizedStripChain bs ν μ) (s : Tableau a ν) (t : Tableau n μ)
    (e : Fin n ≃ Fin a ⊕ Fin b)
    (σ : Representation ℂ (Equiv.Perm (Fin a)) Y)
    (K : Representation.IntertwiningMap (spechtRep s) σ) (hK : K ≠ 0) :
    ∃ c : Fin b → Fin bs.length, (∀ j, wordContent c j = bs.get j) ∧
      ∃ L : Representation.IntertwiningMap ((spechtRep t).comp (sumPermHom e))
        (outer σ (cyclic (wordRep b bs.length) (Pi.single c 1)).toRepresentation), L ≠ 0 := by
  obtain ⟨c,F,hF,hc,hFe⟩ := placed_strip_restriction_counts hs s t e
  let F₀ := K.toLinearMap.comp F
  have hFa (h : Equiv.Perm (Fin a)) (x : Specht t) :
      F₀ (spechtRep t (sumPerm e h 1) x) = σ h (F₀ x) := by
    change K (F (spechtRep t (sumPerm e h 1) x)) = σ h (K (F x))
    rw [hFe h 1 rfl,K.isIntertwining]
  let L : Representation.IntertwiningMap ((spechtRep t).comp (sumPermHom e))
      (outer σ (cyclic (wordRep b bs.length) (Pi.single c 1)).toRepresentation) := {
    toLinearMap := orbitTensorMap e (spechtRep t) c F₀
    isIntertwining' g := by
      apply LinearMap.ext
      intro x
      apply orbitTensorEval_injective c
      ext w
      simp only [LinearMap.comp_apply]
      rw [orbitTensorMap_eval,orbitTensorEval_outer,orbitTensorMap_eval]
      exact bandOrbitMap_equivariant e (spechtRep t) σ c F₀ hFa g.1 g.2 x w }
  refine ⟨c,hc,L,?_⟩
  have hF₀ : F₀ ≠ 0 := by
    intro hz
    apply hK
    ext x
    obtain ⟨y,rfl⟩ := hF x
    exact LinearMap.congr_fun hz y
  have hFb (q : Equiv.Perm (Fin b)) (hq : c ∘ q = c) (x : Specht t) :
      F₀ (spechtRep t (sumPerm e 1 q) x) = F₀ x := by
    change K (F (spechtRep t (sumPerm e 1 q) x)) = K (F x)
    rw [hFe 1 q hq,map_one]
    rfl
  intro hz
  apply bandOrbitMap_nonzero e (spechtRep t) c F₀ hF₀ hFb
  ext x w
  rw [← orbitTensorMap_eval]
  change orbitTensorEval c (L x) w = 0
  rw [hz]
  simp

end Saxl
end
end

end OAI
