import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Balance.BalanceProjection
import OAI.RepresentationTheory.UniversalSquare.Support.Neighboring

namespace OAI

/-! Balance Columns. -/

section

noncomputable section
open scoped TensorProduct

namespace Saxl.Balance

def fixedSumSpace {n d : ℕ} (c : Fin n → ℕ) (z : Fin d → ℤ)
    (σ : ℕ → ℤ) : Submodule ℂ (WordSpace n d) where
  carrier := {x | FixedComponentSums c z σ x}
  zero_mem' := by intro w h; exact False.elim (h rfl)
  add_mem' := by
    intro x y hx hy w hw
    by_cases hh : x w = 0
    · exact hy w (by intro hz; apply hw; simp [hh,hz])
    · exact hx w hh
  smul_mem' := by
    intro a x hx w hw
    exact hx w (by intro hz; apply hw; simp [hz])

lemma component_sum_perm {n : ℕ} (c : Fin n → ℕ) (g : Equiv.Perm (Fin n))
    (hg : g ∈ fiberGroup c) (z : Fin n → ℤ) (k : ℕ) :
    ∑ i ∈ Finset.univ.filter (fun i => c i = k), z (g i) =
      ∑ i ∈ Finset.univ.filter (fun i => c i = k), z i := by
  classical
  have hh : ∀ i, c (g i) = c i := hg
  simpa only [hh] using perm_filter_sum g (fun i => c i = k) z

lemma fixedSumSpace_invariant {n d : ℕ} (c : Fin n → ℕ) (z : Fin d → ℤ)
    (σ : ℕ → ℤ) (g : Equiv.Perm (Fin n)) (hg : g ∈ fiberGroup c)
    (x : WordSpace n d) (hx : x ∈ fixedSumSpace c z σ) :
    wordRep n d g x ∈ fixedSumSpace c z σ := by
  intro w hw k
  have hh := hx (w ∘ g) hw k
  simpa only [Function.comp_apply, component_sum_perm c g hg (fun i => z (w i)) k] using hh

def columnRowSums {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (c : Fin n → ℕ) (k : ℕ) : ℤ :=
  ∑ i ∈ Finset.univ.filter (fun i => c i = k), (rowWord t i).val

def localColumnSub {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) (c : Fin n → ℕ) :=
  cyclic ((wordRep n (μ.colLen 0)).comp (fiberGroup c).subtype) (polytabloid t)

lemma localColumnSub_mem_specht {n : ℕ} {μ : YoungDiagram}
    (t : Tableau n μ) (c : Fin n → ℕ)
    (x : (localColumnSub t c).toSubmodule) : x.val ∈ spechtSub t := by
  rcases x with ⟨x,hx⟩
  change x ∈ Submodule.span ℂ (Set.range fun g : fiberGroup c =>
    wordRep n (μ.colLen 0) g.val (polytabloid t)) at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨g,rfl⟩ := hy
    exact (spechtSub t).apply_mem_toSubmodule g.val (mem_cyclic _ _)
  | zero => exact Submodule.zero_mem _
  | add y z hy hz iy iz => exact Submodule.add_mem _ iy iz
  | smul a y hy iy => exact Submodule.smul_mem _ a iy

lemma polytabloid_fixed_column_sums {n : ℕ} {μ : YoungDiagram}
    (t : Tableau n μ) (c : Fin n → ℕ)
    (hc : ∀ i j, (t i).val.2 = (t j).val.2 → c i = c j) :
    polytabloid t ∈ fixedSumSpace c (fun a : Fin (μ.colLen 0) => a.val)
      (columnRowSums t c) := by
  classical
  have hbase : (Pi.single (rowWord t) (1 : ℂ)) ∈
      fixedSumSpace c (fun a : Fin (μ.colLen 0) => a.val) (columnRowSums t c) := by
    intro w hw k
    have he : w = rowWord t := by
      by_contra hn
      exact hw (Pi.single_eq_of_ne hn _)
    subst w
    rfl
  unfold polytabloid
  apply Submodule.sum_mem
  intro g hg
  apply Submodule.smul_mem
  apply fixedSumSpace_invariant _ _ _ _ ?_ _ hbase
  intro i
  exact hc _ _ (g.property i)

lemma localColumnSub_fixed_sums {n : ℕ} {μ : YoungDiagram}
    (t : Tableau n μ) (c : Fin n → ℕ)
    (hc : ∀ i j, (t i).val.2 = (t j).val.2 → c i = c j)
    (x : (localColumnSub t c).toSubmodule) :
    x.val ∈ fixedSumSpace c (fun a : Fin (μ.colLen 0) => a.val) (columnRowSums t c) := by
  rcases x with ⟨x,hx⟩
  change x ∈ Submodule.span ℂ (Set.range fun g : fiberGroup c =>
    wordRep n (μ.colLen 0) g.val (polytabloid t)) at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨g,rfl⟩ := hy
    exact fixedSumSpace_invariant _ _ _ g.val g.property _
      (polytabloid_fixed_column_sums t c hc)
  | zero => exact Submodule.zero_mem _
  | add y z hy hz iy iz => exact Submodule.add_mem _ iy iz
  | smul a y hy iy => exact Submodule.smul_mem _ a iy

def localColumnTensorMap {n : ℕ} {μ : YoungDiagram}
    (t : Tableau n μ) (c : Fin n → ℕ) :
    Representation.IntertwiningMap
      ((localColumnSub t c).toRepresentation.tprod (localColumnSub t c).toRepresentation)
      ((wordRep n (μ.colLen 0 * μ.colLen 0)).comp (fiberGroup c).subtype) where
  toLinearMap := (wordTensor n (μ.colLen 0) (μ.colLen 0)).toLinearMap.comp
    (TensorProduct.map (localColumnSub t c).toSubmodule.subtype
      (localColumnSub t c).toSubmodule.subtype)
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x y =>
      change wordTensor _ _ _
        (wordRep n (μ.colLen 0) g.val x.val ⊗ₜ[ℂ] wordRep n (μ.colLen 0) g.val y.val) = _
      exact wordTensor_equivariant g.val (x.val ⊗ₜ[ℂ] y.val)

lemma localColumnTensorMap_tmul {n : ℕ} {μ : YoungDiagram}
    (t : Tableau n μ) (c : Fin n → ℕ)
    (x y : (localColumnSub t c).toSubmodule) :
    localColumnTensorMap t c (x ⊗ₜ[ℂ] y) = wordTensor _ _ _ (x.val ⊗ₜ[ℂ] y.val) := rfl

lemma localColumnTensorMap_mem {n : ℕ} {μ : YoungDiagram}
    (t : Tableau n μ) (c : Fin n → ℕ)
    (x : (localColumnSub t c).toSubmodule ⊗[ℂ] (localColumnSub t c).toSubmodule) :
    localColumnTensorMap t c x ∈ (spechtTensorMap t t).range := by
  change localColumnTensorMap t c x ∈ (spechtTensorMap t t).range.toSubmodule
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  | tmul x y =>
    refine ⟨(⟨x.val,localColumnSub_mem_specht t c x⟩ : Specht t) ⊗ₜ[ℂ]
      (⟨y.val,localColumnSub_mem_specht t c y⟩ : Specht t), ?_⟩
    rw [spechtTensorMap]
    rfl

def columnOutputSums {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (c : Fin n → ℕ) (k : ℕ) : ℤ :=
  2 * columnRowSums t c k + (Finset.univ.filter (fun i => c i = k)).card

theorem localColumnTensorMap_fixed_sums {n : ℕ} {μ : YoungDiagram}
    (t : Tableau n μ) (c : Fin n → ℕ)
    (hc : ∀ i j, (t i).val.2 = (t j).val.2 → c i = c j)
    (x : (localColumnSub t c).toSubmodule ⊗[ℂ] (localColumnSub t c).toSubmodule) :
    localColumnTensorMap t c x ∈ fixedSumSpace c
      (fun a : Fin (μ.colLen 0 * μ.colLen 0) => (output a : ℤ)) (columnOutputSums t c) := by
  classical
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  | tmul x y =>
    intro w hw k
    rw [localColumnTensorMap_tmul, wordTensor_tmul] at hw
    obtain ⟨hx,hy⟩ := mul_ne_zero_iff.mp hw
    have hs₁ := localColumnSub_fixed_sums t c hc x (splitLeft w) hx k
    have hs₂ := localColumnSub_fixed_sums t c hc y (splitRight w) hy k
    change (∑ i ∈ Finset.univ.filter (fun i => c i = k),
      (output (w i) : ℤ)) = _
    simp only [output, Nat.cast_add, Nat.cast_one, Finset.sum_add_distrib,
      Finset.sum_const, nsmul_eq_mul, mul_one]
    change (∑ i ∈ Finset.univ.filter (fun i => c i = k), ((splitLeft w i).val : ℤ)) +
      (∑ i ∈ Finset.univ.filter (fun i => c i = k), ((splitRight w i).val : ℤ)) +
      _ = _
    rw [hs₁,hs₂]
    dsimp only [columnOutputSums]
    ring

lemma componentWords_invariant_fiber {n d : ℕ} (c : Fin n → ℕ)
    (A : Fin d → Prop) (label : Fin d → ℕ) (g : Equiv.Perm (Fin n))
    (hg : g ∈ fiberGroup c) (w : Fin n → Fin d) :
    componentWords c A label (w ∘ g) ↔ componentWords c A label w := by
  constructor
  · rintro ⟨hA,hl⟩
    refine ⟨?_, fun i => ?_⟩
    · intro i
      simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hA (g.symm i)
    · have he := hl (g.symm i)
      have hc := hg (g.symm i)
      simpa only [Function.comp_apply, Equiv.apply_symm_apply] using he.trans hc.symm
  · rintro ⟨hA,hl⟩
    exact ⟨fun i => hA (g i),fun i => (hl (g i)).trans (hg i)⟩

def componentProjection {n d : ℕ} (c : Fin n → ℕ)
    (A : Fin d → Prop) (label : Fin d → ℕ) :
    Representation.IntertwiningMap
      ((wordRep n d).comp (fiberGroup c).subtype)
      ((wordRep n d).comp (fiberGroup c).subtype) where
  toLinearMap := coordinateProjection (componentWords c A label)
  isIntertwining' g := by
    classical
    apply LinearMap.ext
    intro x
    funext w
    change (if componentWords c A label w then x (w ∘ g.val) else 0) =
      (if componentWords c A label (w ∘ g.val) then x (w ∘ g.val) else 0)
    rw [componentWords_invariant_fiber c A label g.val g.property]

def projectedColumnSquare {n : ℕ} {μ : YoungDiagram}
    (t : Tableau n μ) (c : Fin n → ℕ)
    (A : Fin (μ.colLen 0 * μ.colLen 0) → Prop)
    (label : Fin (μ.colLen 0 * μ.colLen 0) → ℕ) :=
  ((componentProjection c A label).comp (localColumnTensorMap t c)).range

def rangeQuotient {G X Y : Type*} [Group G]
    [AddCommMonoid X] [Module ℂ X] [AddCommMonoid Y] [Module ℂ Y]
    {ρ : Representation ℂ G X} {σ : Representation ℂ G Y}
    (F : Representation.IntertwiningMap ρ σ) :
    Representation.IntertwiningMap ρ F.range.toRepresentation where
  toLinearMap := F.toLinearMap.rangeRestrict
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact LinearMap.congr_fun (F.isIntertwining' g) x

lemma rangeQuotient_surjective {G X Y : Type*} [Group G]
    [AddCommMonoid X] [Module ℂ X] [AddCommMonoid Y] [Module ℂ Y]
    {ρ : Representation ℂ G X} {σ : Representation ℂ G Y}
    (F : Representation.IntertwiningMap ρ σ) : Function.Surjective (rangeQuotient F) := by
  rintro ⟨y,x,rfl⟩
  exact ⟨x,rfl⟩

theorem projected_range_support {n d : ℕ} {X Y : Type*}
    [AddCommGroup X] [Module ℂ X] [AddCommMonoid Y] [Module ℂ Y]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    (W : Subrepresentation (wordRep n d))
    (c : Fin n → ℕ) (A : Fin d → Prop) (label : Fin d → ℕ)
    (z : Fin d → ℤ) (σ : ℕ → ℤ)
    (ho : ∀ a b, A a → A b → label a < label b → z a < z b)
    (τ : Representation ℂ (fiberGroup c) Y)
    (J : Representation.IntertwiningMap τ ((wordRep n d).comp (fiberGroup c).subtype))
    (hm : ∀ y, J y ∈ W) (hs : ∀ y, FixedComponentSums c z σ (J y))
    (f : Representation.IntertwiningMap (ρ.comp (fiberGroup c).subtype)
      ((componentProjection c A label).comp J).range.toRepresentation) (hf : f ≠ 0) :
    ∃ F : Representation.IntertwiningMap ρ W.toRepresentation, F ≠ 0 := by
  let : AddCommGroup Y := Module.addCommMonoidToAddCommGroup ℂ
  let Q := (componentProjection c A label).comp J
  obtain ⟨h,hh⟩ := intertwining_lift_surjective (rangeQuotient Q)
    (rangeQuotient_surjective Q) f
  let L := J.toLinearMap.comp h.toLinearMap
  have he (x : X) : coordinateProjection (componentWords c A label) (L x) = (f x).val :=
    congrArg Subtype.val (congrArg (fun T : Representation.IntertwiningMap
      (ρ.comp (fiberGroup c).subtype) Q.range.toRepresentation => T x) hh)
  have hL : (coordinateProjection (componentWords c A label)).comp L ≠ 0 := by
    intro hz
    apply hf
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact (he x).symm.trans (LinearMap.congr_fun hz x)
  have heq (g : Equiv.Perm (Fin n)) (hg : g ∈ fiberGroup c) (x : X) :
      coordinateProjection (componentWords c A label) (L (ρ g x)) =
        wordRep n d g (coordinateProjection (componentWords c A label) (L x)) := by
    rw [he,he]
    exact congrArg Subtype.val (LinearMap.congr_fun (f.isIntertwining' ⟨g,hg⟩) x)
  exact balance_support_transfer ρ W c A label z σ ho L
    (fun x => hm (h x)) (fun x => hs (h x)) hL heq

theorem projected_columns_support {n : ℕ} {μ : YoungDiagram} {X : Type*}
    [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    (t : Tableau n μ) (c : Fin n → ℕ)
    (hc : ∀ i j, (t i).val.2 = (t j).val.2 → c i = c j)
    (A : Fin (μ.colLen 0 * μ.colLen 0) → Prop)
    (label : Fin (μ.colLen 0 * μ.colLen 0) → ℕ)
    (ho : ∀ a b, A a → A b → label a < label b → output a < output b)
    (f : Representation.IntertwiningMap (ρ.comp (fiberGroup c).subtype)
      (projectedColumnSquare t c A label).toRepresentation) (hf : f ≠ 0) :
    ∃ F : Representation.IntertwiningMap ρ ((spechtRep t).tprod (spechtRep t)), F ≠ 0 := by
  have hR : ∃ F : Representation.IntertwiningMap ρ (spechtTensorMap t t).range.toRepresentation,
      F ≠ 0 := by
    apply projected_range_support ρ (spechtTensorMap t t).range c A label
      (fun a => (output (d := μ.colLen 0) (e := μ.colLen 0) a : ℤ))
      (columnOutputSums t c) _
      ((localColumnSub t c).toRepresentation.tprod (localColumnSub t c).toRepresentation)
      (localColumnTensorMap t c) _ _ f hf
    · intro a b ha hb hab
      exact_mod_cast ho a b ha hb hab
    · intro y
      exact localColumnTensorMap_mem t c y
    · intro y
      exact localColumnTensorMap_fixed_sums t c hc y
  obtain ⟨F,hF⟩ := hR
  let : AddCommGroup (Specht t ⊗[ℂ] Specht t) := Module.addCommMonoidToAddCommGroup ℂ
  obtain ⟨i,hi⟩ := subrepresentation_embeds_of_le_range (spechtTensorMap t t)
    (spechtTensorMap t t).range le_rfl
  exact ⟨i.comp F,intertwining_comp_ne_zero i hi F hF⟩

theorem kronecker_pos_of_projected_columns {n : ℕ} {μ ν : YoungDiagram}
    (t : Tableau n μ) (s : Tableau n ν) (c : Fin n → ℕ)
    (hc : ∀ i j, (t i).val.2 = (t j).val.2 → c i = c j)
    (A : Fin (μ.colLen 0 * μ.colLen 0) → Prop)
    (label : Fin (μ.colLen 0 * μ.colLen 0) → ℕ)
    (ho : ∀ a b, A a → A b → label a < label b → output a < output b)
    (f : Representation.IntertwiningMap ((spechtRep s).comp (fiberGroup c).subtype)
      (projectedColumnSquare t c A label).toRepresentation) (hf : f ≠ 0) :
    0 < kronecker t t s :=
  (kronecker_pos_iff t t s).mpr (projected_columns_support (spechtRep s) t c hc A label ho f hf)

end Saxl.Balance
end
end

end OAI
