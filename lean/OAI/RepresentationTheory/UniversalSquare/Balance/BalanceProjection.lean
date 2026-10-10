import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Balance.BalanceSeparation
import OAI.RepresentationTheory.UniversalSquare.Support.ProjectedTensor

namespace OAI

/-! Balance Projection. -/

section

noncomputable section
namespace Saxl.Balance

def FixedComponentSums {n d : ℕ} (c : Fin n → ℕ) (z : Fin d → ℤ)
    (σ : ℕ → ℤ) (x : WordSpace n d) : Prop :=
  ∀ w, x w ≠ 0 → ∀ k, ∑ i ∈ Finset.univ.filter (fun i => c i = k), z (w i) = σ k

def balanceWords {n d : ℕ} (c : Fin n → ℕ) (A : Fin d → Prop)
    (label : Fin d → ℕ) (z : Fin d → ℤ) (σ : ℕ → ℤ)
    (w : Fin n → Fin d) : Prop :=
  (∀ i, A (w i)) ∧ ∀ k,
    (Finset.univ.filter (fun i => label (w i) = k)).card =
      (Finset.univ.filter (fun i => c i = k)).card ∧
    ∑ i ∈ Finset.univ.filter (fun i => label (w i) = k), z (w i) = σ k

def componentWords {n d : ℕ} (c : Fin n → ℕ) (A : Fin d → Prop)
    (label : Fin d → ℕ) (w : Fin n → Fin d) : Prop :=
  (∀ i, A (w i)) ∧ ∀ i, label (w i) = c i

lemma perm_filter_card {X : Type*} [Fintype X] [DecidableEq X]
    (g : Equiv.Perm X) (p : X → Prop) [DecidablePred p] :
    (Finset.univ.filter (fun x => p (g x))).card = (Finset.univ.filter p).card := by
  classical
  apply Finset.card_bij (fun x _ => g x)
  · intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩
  · intro x hx y hy hxy
    exact g.injective hxy
  · intro y hy
    refine ⟨g.symm y, ?_, g.apply_symm_apply y⟩
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.apply_symm_apply]
      using (Finset.mem_filter.mp hy).2

lemma perm_filter_sum {X : Type*} [Fintype X] [DecidableEq X]
    (g : Equiv.Perm X) (p : X → Prop) [DecidablePred p] (f : X → ℤ) :
    ∑ i ∈ Finset.univ.filter (fun i => p (g i)), f (g i) =
      ∑ i ∈ Finset.univ.filter p, f i := by
  simpa only [Finset.sum_filter] using
    Equiv.sum_comp g (fun i => if p i then f i else 0)

lemma balanceWords_invariant {n d : ℕ} (c : Fin n → ℕ) (A : Fin d → Prop)
    (label : Fin d → ℕ) (z : Fin d → ℤ) (σ : ℕ → ℤ)
    (g : Equiv.Perm (Fin n)) (w : Fin n → Fin d) :
    balanceWords c A label z σ (w ∘ g) ↔ balanceWords c A label z σ w := by
  classical
  unfold balanceWords
  have hc (k) := perm_filter_card g (fun i => label (w i) = k)
  have hs (k) := perm_filter_sum g (fun i => label (w i) = k) (fun i => z (w i))
  simp only [Function.comp_apply, hc, hs]
  constructor
  · rintro ⟨h,hc⟩
    exact ⟨fun i => by simpa using h (g.symm i),hc⟩
  · rintro ⟨h,hc⟩
    exact ⟨fun i => h (g i),hc⟩

lemma balanceWords_iff_components {n d : ℕ} (c : Fin n → ℕ) (A : Fin d → Prop)
    (label : Fin d → ℕ) (z : Fin d → ℤ) (σ : ℕ → ℤ)
    (ho : ∀ a b, A a → A b → label a < label b → z a < z b)
    (w : Fin n → Fin d)
    (hw : ∀ k, ∑ i ∈ Finset.univ.filter (fun i => c i = k), z (w i) = σ k) :
    balanceWords c A label z σ w ↔ componentWords c A label w := by
  classical
  constructor
  · rintro ⟨hA,hcs⟩
    refine ⟨hA,fun i => ?_⟩
    exact (ordered_output_labels_eq Finset.univ c (fun i => label (w i))
      (fun i => z (w i)) (fun i hi j hj hh => ho _ _ (hA i) (hA j) hh)
      (fun k => (hcs k).1.symm) (fun k => (hw k).trans (hcs k).2.symm)
      i (Finset.mem_univ i)).symm
  · rintro ⟨hA,hl⟩
    refine ⟨hA, fun k => ?_⟩
    simp only [hl]
    exact ⟨True.intro,hw k⟩

theorem balance_projection_eq {n d : ℕ} (c : Fin n → ℕ) (A : Fin d → Prop)
    (label : Fin d → ℕ) (z : Fin d → ℤ) (σ : ℕ → ℤ)
    (ho : ∀ a b, A a → A b → label a < label b → z a < z b)
    (x : WordSpace n d) (hx : FixedComponentSums c z σ x) :
    coordinateProjection (balanceWords c A label z σ) x =
      coordinateProjection (componentWords c A label) x := by
  classical
  funext w
  by_cases hw : x w = 0
  · simp only [coordinateProjection_apply, hw, ite_self]
  · simp only [coordinateProjection_apply,
      balanceWords_iff_components c A label z σ ho w (hx w hw)]

theorem component_projection_mem {n d : ℕ} (c : Fin n → ℕ) (A : Fin d → Prop)
    (label : Fin d → ℕ) (z : Fin d → ℤ) (σ : ℕ → ℤ)
    (ho : ∀ a b, A a → A b → label a < label b → z a < z b)
    (W : Subrepresentation (wordRep n d)) (x : WordSpace n d)
    (hxW : x ∈ W) (hx : FixedComponentSums c z σ x) :
    coordinateProjection (componentWords c A label) x ∈
      ((invariantCoordinateProjection (balanceWords c A label z σ)
        (balanceWords_invariant c A label z σ)).comp (subrepInclusion W)).range := by
  refine ⟨⟨x,hxW⟩, ?_⟩
  exact balance_projection_eq c A label z σ ho x hx

theorem components_support_transfer {n d : ℕ} {X : Type*}
    [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    (W : Subrepresentation (wordRep n d))
    (c : Fin n → ℕ) (A : Fin d → Prop) (label : Fin d → ℕ)
    (f : X →ₗ[ℂ] WordSpace n d) (hf : f ≠ 0)
    (he : ∀ g ∈ fiberGroup c, ∀ x, f (ρ g x) = wordRep n d g (f x))
    (hm : ∀ x, f x ∈ W)
    (hs : ∀ x w, f x w ≠ 0 → componentWords c A label w) :
    ∃ F : Representation.IntertwiningMap ρ W.toRepresentation, F ≠ 0 := by
  classical
  let P := coordinateProjection (componentWords c A label)
  have hP (x) : P (f x) = f x := by
    ext w
    change (if componentWords c A label w then f x w else 0) = _
    split_ifs with h
    · rfl
    · exact (not_ne_iff.mp (fun hh => h (hs x w hh))).symm
  have hk (g : Equiv.Perm (Fin n)) (hg : g ∉ fiberGroup c) (x) :
      P (wordRep n d g (f x)) = 0 := by
    ext w
    change (if componentWords c A label w then f x (w ∘ g) else 0) = 0
    split_ifs with hw
    · by_contra hn
      have hh := hs x (w ∘ g) hn
      apply hg
      intro i
      exact (hw.2 (g i)).symm.trans (hh.2 i)
    · rfl
  let F := averagedMap ρ (wordRep n d) f
  have hF : F ≠ 0 := sector_average_nonzero ρ (wordRep n d) (fiberGroup c) f hf he P hP hk
  have hmem (x) : F x ∈ W := by
    rw [show F x = _ from averagedMap_apply ρ (wordRep n d) f x]
    apply Submodule.sum_mem
    intro g hg
    exact W.apply_mem_toSubmodule g (hm _)
  let T : Representation.IntertwiningMap ρ W.toRepresentation :=
    { toLinearMap := F.toLinearMap.codRestrict _ hmem
      isIntertwining' := by
        intro g
        apply LinearMap.ext
        intro x
        apply Subtype.ext
        exact LinearMap.congr_fun (F.isIntertwining' g) x }
  refine ⟨T, ?_⟩
  intro hz
  apply hF
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  exact congrArg Subtype.val (congrArg (fun l => l x) hz)

theorem balance_support_transfer {n d : ℕ} {X : Type*}
    [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    (W : Subrepresentation (wordRep n d))
    (c : Fin n → ℕ) (A : Fin d → Prop) (label : Fin d → ℕ)
    (z : Fin d → ℤ) (σ : ℕ → ℤ)
    (ho : ∀ a b, A a → A b → label a < label b → z a < z b)
    (L : X →ₗ[ℂ] WordSpace n d)
    (hm : ∀ x, L x ∈ W) (hσ : ∀ x, FixedComponentSums c z σ (L x))
    (hf : (coordinateProjection (componentWords c A label)).comp L ≠ 0)
    (he : ∀ g ∈ fiberGroup c, ∀ x,
      coordinateProjection (componentWords c A label) (L (ρ g x)) =
      wordRep n d g (coordinateProjection (componentWords c A label) (L x))) :
    ∃ F : Representation.IntertwiningMap ρ W.toRepresentation, F ≠ 0 := by
  classical
  let P := (invariantCoordinateProjection (balanceWords c A label z σ)
    (balanceWords_invariant c A label z σ)).comp (subrepInclusion W)
  let f := (coordinateProjection (componentWords c A label)).comp L
  have hmem (x) : f x ∈ P.range :=
    component_projection_mem c A label z σ ho W (L x) (hm x) (hσ x)
  have hsector (x w) (hw : f x w ≠ 0) : componentWords c A label w := by
    by_contra hn
    exact hw (by change (if componentWords c A label w then L x w else 0) = 0; rw [ite_eq_right hn])
  obtain ⟨T,hT⟩ := components_support_transfer ρ P.range c A label f hf he hmem hsector
  obtain ⟨i,hi⟩ := subrepresentation_embeds_of_le_range P P.range le_rfl
  refine ⟨i.comp T, ?_⟩
  exact intertwining_comp_ne_zero i hi T hT

end Saxl.Balance
end
end

end OAI
