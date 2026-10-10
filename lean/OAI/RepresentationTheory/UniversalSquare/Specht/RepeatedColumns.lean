import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Contraction.SquareDetection

namespace OAI

/-! Repeated Columns. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

lemma paired_relation_iff_free {n d e : ℕ} (H : Subgroup (Equiv.Perm (Fin n)))
    (a : Fin n → Fin d) (t : Fin n → Fin e) (ω : H)
    (ht : ∀ g : H, ∀ i, t (g.val i) = t i)
    (ha : ∀ g h : H, a ∘ g.val = a ∘ h.val → g = h)
    (hω : ∀ i, (a i).val + (a (ω.val i)).val = (t i).val) (g h : H) :
    (∀ i, (a (g.val i)).val + (a (h.val i)).val = (t i).val) ↔ h = ω*g := by
  constructor
  · intro hh
    apply ha
    funext i
    apply Fin.ext
    have he := hω (g.val i)
    rw [ht g i] at he
    exact Nat.add_left_cancel ((hh i).trans he.symm)
  · rintro rfl i
    have he := hω (g.val i)
    rw [ht g i] at he
    exact he

lemma paired_term_projection_free {n d e : ℕ} (H : Subgroup (Equiv.Perm (Fin n)))
    (a : Fin n → Fin d) (t : Fin n → Fin e) (ω : H)
    (ht : ∀ g : H, ∀ i, t (g.val i) = t i)
    (ha : ∀ g h : H, a ∘ g.val = a ∘ h.val → g = h)
    (hω : ∀ i, (a i).val + (a (ω.val i)).val = (t i).val) (g h : H) :
    orbitProjection t (pairSumMap n d e (Pi.single
      (mergeWords (a ∘ g.val) (a ∘ h.val)) 1)) =
      if h = ω*g then Pi.single t 1 else 0 := by
  classical
  ext c
  change (if wordOrbit t c then pairSumMap n d e (Pi.single
      (mergeWords (a ∘ g.val) (a ∘ h.val)) 1) c else 0) = _
  rw [pairSumMap_single]
  simp only [Function.comp_apply]
  by_cases he : h = ω*g
  · rw [ite_eq_left he]
    have hr := (paired_relation_iff_free H a t ω ht ha hω g h).mpr he
    by_cases hc : c = t
    · subst c
      rw [ite_eq_left ⟨1, rfl⟩, ite_eq_left hr]
      simp
    · rw [Pi.single_eq_of_ne hc]
      have hn : ¬ ∀ i, (a (g.val i)).val + (a (h.val i)).val = (c i).val := by
        intro hh
        apply hc
        funext i
        exact Fin.ext ((hh i).symm.trans (hr i))
      simp only [hn, ite_false, ite_self]
  · rw [ite_eq_right he]
    change (if wordOrbit t c then _ else _) = (0:ℂ)
    by_cases ho : wordOrbit t c
    · rw [ite_eq_left ho]
      apply ite_eq_right
      intro hh
      obtain ⟨k,hk⟩ := ho
      have heq : (fun i => ((c i).val : ℝ)) = fun i => ((t i).val : ℝ) := by
        apply pair_sum_rigidity (fun i => ((a i).val : ℝ)) (fun i => ((t i).val : ℝ))
          (fun i => ((c i).val : ℝ)) ω.val g.val h.val k
        · intro i; rw [ht ω i]
        · intro i; exact_mod_cast hω i
        · intro i; rw [ht g i]
        · intro i; rw [ht h i]
        · intro i; exact_mod_cast (hh i).symm
        · intro i; rw [hk]; rfl
      have hct : c = t := by
        funext i
        apply Fin.ext
        exact_mod_cast congrFun heq i
      rw [hct] at hh
      exact he ((paired_relation_iff_free H a t ω ht ha hω g h).mp hh)
    · rw [ite_eq_right ho]

theorem repeated_alt_projection_free {n d e : ℕ} (H : Subgroup (Equiv.Perm (Fin n)))
    (a : Fin n → Fin d) (t : Fin n → Fin e) (ω : H)
    (ht : ∀ g : H, ∀ i, t (g.val i) = t i)
    (ha : ∀ g h : H, a ∘ g.val = a ∘ h.val → g = h)
    (hω : ∀ i, (a i).val + (a (ω.val i)).val = (t i).val) :
    orbitProjection t (pairSumMap n d e (wordTensor n d d
      (altWord H a ⊗ₜ[ℂ] altWord H a))) =
      ((Nat.card H : ℂ) * signC ω.val) • Pi.single t 1 := by
  classical
  let := Fintype.ofFinite H
  rw [altWord_inverse_sum, TensorProduct.sum_tmul]
  simp only [TensorProduct.tmul_sum, map_sum, TensorProduct.smul_tmul_smul, map_smul,
    wordTensor_single, paired_term_projection_free H a t ω ht ha hω]
  simp only [smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hs (g : H) : signC g.val * signC (ω*g).val = signC ω.val := by
    simp only [Subgroup.coe_mul, map_mul]
    calc
      signC g.val * (signC ω.val * signC g.val) = signC ω.val * (signC g.val * signC g.val) := by ring
      _ = signC ω.val := by rw [signC_mul_self, mul_one]
  simp only [hs, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, Fintype.card_eq_nat_card]

def columnReversalCell (α : YoungDiagram) (x : α.cells) : α.cells :=
  ⟨(α.colLen x.val.2 - 1 - x.val.1, x.val.2), by
    have hx : x.val.1 < α.colLen x.val.2 := YoungDiagram.mem_iff_lt_colLen.mp x.property
    apply YoungDiagram.mem_iff_lt_colLen.mpr
    omega⟩

lemma columnReversalCell_involutive (α : YoungDiagram) :
    Function.Involutive (columnReversalCell α) := by
  intro x
  have hx : x.val.1 < α.colLen x.val.2 := YoungDiagram.mem_iff_lt_colLen.mp x.property
  apply Subtype.ext
  apply Prod.ext
  · change α.colLen x.val.2 - 1 - (α.colLen x.val.2 - 1 - x.val.1) = x.val.1
    omega
  · rfl

def columnReversalEquiv (α : YoungDiagram) : Equiv.Perm α.cells :=
  ⟨columnReversalCell α, columnReversalCell α,
    columnReversalCell_involutive α, columnReversalCell_involutive α⟩

def columnReversal {n : ℕ} {α : YoungDiagram} (t : Tableau n α) : columnGroup t :=
  ⟨(t.trans (columnReversalEquiv α)).trans t.symm, by
    intro i
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
    rfl⟩

def columnLengthWord {n : ℕ} {α : YoungDiagram} (t : Tableau n α) :
    Fin n → Fin (α.colLen 0) := fun i =>
  ⟨α.colLen (t i).val.2 - 1, by
    have hx : (t i).val.1 < α.colLen (t i).val.2 :=
      YoungDiagram.mem_iff_lt_colLen.mp (t i).property
    have hy := α.colLen_anti 0 (t i).val.2 (Nat.zero_le _)
    omega⟩

lemma columnLengthWord_fixed {n : ℕ} {α : YoungDiagram} (t : Tableau n α)
    (g : columnGroup t) (i) : columnLengthWord t (g.val i) = columnLengthWord t i := by
  apply Fin.ext
  change α.colLen (t (g.val i)).val.2 - 1 = α.colLen (t i).val.2 - 1
  rw [g.property i]

lemma rowWord_column_free {n : ℕ} {α : YoungDiagram} (t : Tableau n α)
    (g h : columnGroup t) (he : rowWord t ∘ g.val = rowWord t ∘ h.val) : g = h := by
  apply Subtype.ext
  apply Equiv.ext
  intro i
  apply t.injective
  apply Subtype.ext
  exact Prod.ext (congrArg Fin.val (congrFun he i)) ((g.property i).trans (h.property i).symm)

lemma columnReversal_complement {n : ℕ} {α : YoungDiagram} (t : Tableau n α) (i) :
    (rowWord t i).val + (rowWord t ((columnReversal t).val i)).val =
      (columnLengthWord t i).val := by
  have hx : (t i).val.1 < α.colLen (t i).val.2 :=
      YoungDiagram.mem_iff_lt_colLen.mp (t i).property
  change (t i).val.1 + (t (t.symm (columnReversalCell α (t i)))).val.1 =
    α.colLen (t i).val.2 - 1
  rw [Equiv.apply_symm_apply]
  change (t i).val.1 + (α.colLen (t i).val.2 - 1 - (t i).val.1) =
    α.colLen (t i).val.2 - 1
  omega

theorem squared_polytabloid_projection {n : ℕ} {α : YoungDiagram} (t : Tableau n α) :
    orbitProjection (columnLengthWord t)
      (pairSumMap n (α.colLen 0) (α.colLen 0)
        (wordTensor n (α.colLen 0) (α.colLen 0) (polytabloid t ⊗ₜ[ℂ] polytabloid t))) =
      ((Nat.card (columnGroup t) : ℂ) * signC (columnReversal t).val) •
        Pi.single (columnLengthWord t) 1 := by
  simp only [polytabloid_eq_altWord]
  exact repeated_alt_projection_free (columnGroup t) (rowWord t) (columnLengthWord t)
    (columnReversal t) (columnLengthWord_fixed t) (rowWord_column_free t)
    (columnReversal_complement t)

lemma column_projection_coefficient_ne_zero {n : ℕ} {α : YoungDiagram} (t : Tableau n α) :
    (Nat.card (columnGroup t) : ℂ) * signC (columnReversal t).val ≠ 0 := by
  apply mul_ne_zero
  · exact Nat.cast_ne_zero.mpr (Nat.card_pos.ne')
  · intro hz
    have hh := signC_mul_self (columnReversal t).val
    rw [hz, zero_mul] at hh
    exact zero_ne_one hh

theorem specht_map_back_of_nonzero {n : ℕ} {μ : YoungDiagram}
    {X : Type*} [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) X) (t : Tableau n μ)
    (F : Representation.IntertwiningMap ρ (spechtRep t)) (hF : F ≠ 0) :
    ∃ f : Representation.IntertwiningMap (spechtRep t) ρ, f ≠ 0 := by
  let := specht_irreducible t
  have hs : Function.Surjective F :=
    (Representation.IsIrreducible.surjective_or_eq_zero F).resolve_right hF
  obtain ⟨f, hf⟩ := intertwining_lift_surjective F hs
    (Representation.IntertwiningMap.id (spechtRep t))
  refine ⟨f, ?_⟩
  intro hz
  have he := congrArg (fun H : Representation.IntertwiningMap (spechtRep t) (spechtRep t) =>
    H ⟨polytabloid t, mem_cyclic _ _⟩) hf
  change F (f _) = _ at he
  rw [hz] at he
  change F 0 = _ at he
  rw [map_zero] at he
  exact polytabloid_ne_zero t (congrArg Subtype.val he.symm)

theorem kronecker_pos_of_column_content {n : ℕ} {α μ : YoungDiagram}
    (a : Tableau n α) (t : Tableau n μ) (θ : YoungDiagram)
    (hc : μ.card = θ.card) (hd : Dominates μ θ)
    (f : Fin (α.colLen 0) → Fin (θ.colLen 0))
    (hw : ∀ j, (Finset.univ.filter (fun i => f (columnLengthWord a i) = j)).card =
      θ.rowLen j) : 0 < kronecker a a t := by
  classical
  let w := f ∘ columnLengthWord a
  obtain ⟨F, hF⟩ := young_orbit_map θ μ t hc hd w (Equiv.refl _) hw
  let P : Representation.IntertwiningMap ((spechtRep a).tprod (spechtRep a))
      (wordRep n (θ.colLen 0)) := (letterLift f).comp ((orbitProjection (columnLengthWord a)).comp
    ((pairSumMap n (α.colLen 0) (α.colLen 0)).comp (spechtTensorMap a a)))
  let Q : Representation.IntertwiningMap ((spechtRep a).tprod (spechtRep a))
      (spechtRep t) := F.comp P
  let v : Specht a := ⟨polytabloid a, mem_cyclic _ _⟩
  have hp : P (v ⊗ₜ[ℂ] v) =
      ((Nat.card (columnGroup a) : ℂ) * signC (columnReversal a).val) •
        Pi.single w 1 := by
    change letterLift f (orbitProjection _ (pairSumMap _ _ _
      (spechtTensorMap a a (v ⊗ₜ[ℂ] v)))) = _
    have he : spechtTensorMap a a (v ⊗ₜ[ℂ] v) =
        wordTensor _ _ _ (polytabloid a ⊗ₜ[ℂ] polytabloid a) := by
      unfold spechtTensorMap
      rfl
    rw [he, squared_polytabloid_projection, map_smul, letterLift_single]
  have hQ : Q ≠ 0 := by
    intro hz
    have hh := congrArg (fun H => H (v ⊗ₜ[ℂ] v)) hz
    change F (P (v ⊗ₜ[ℂ] v)) = 0 at hh
    rw [hp, map_smul] at hh
    exact (smul_ne_zero (column_projection_coefficient_ne_zero a) hF) hh
  apply (kronecker_pos_iff a a t).mpr
  exact specht_map_back_of_nonzero (X := Specht a ⊗[ℂ] Specht a)
    ((spechtRep a).tprod (spechtRep a)) t Q hQ

lemma tableau_count {n : ℕ} {α : YoungDiagram} (t : Tableau n α)
    (P : ℕ × ℕ → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun i => P (t i).val)).card = (α.cells.filter P).card := by
  classical
  apply Finset.card_bij (fun i _ => (t i).val)
  · intro i hi
    exact Finset.mem_filter.mpr ⟨(t i).property, (Finset.mem_filter.mp hi).2⟩
  · intro i hi j hj he
    exact t.injective (Subtype.ext he)
  · intro x hx
    have hxα := (Finset.mem_filter.mp hx).1
    refine ⟨t.symm ⟨x, hxα⟩, ?_, ?_⟩
    · simpa only [Equiv.apply_symm_apply, Finset.mem_filter, Finset.mem_univ,
        true_and] using (Finset.mem_filter.mp hx).2
    · simp only [Equiv.apply_symm_apply]

end Saxl
end
end

end OAI
