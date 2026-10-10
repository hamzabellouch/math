import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Specht.ColumnRestriction
import OAI.RepresentationTheory.UniversalSquare.Balance.BalancedColumns
import OAI.RepresentationTheory.UniversalSquare.Support.SignedInduction

namespace OAI

/-! Two Extras. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

lemma cyclicMap_injective {G X Y : Type*} [Group G] [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] {ρ : Representation ℂ G X} {σ : Representation ℂ G Y}
    (F : Representation.IntertwiningMap ρ σ) (v : X) (hF : Function.Injective F) :
    Function.Injective (cyclicMap F v) := by
  intro x y h
  apply Subtype.ext
  exact hF (congrArg Subtype.val h)

lemma cyclic_positionProduct_eq {n a b d : ℕ} (e e' : Fin n ≃ Fin a ⊕ Fin b)
    (v : WordSpace a d) (w : WordSpace b d) :
    cyclic (wordRep n d) (positionProduct e v w) =
      cyclic (wordRep n d) (positionProduct e' v w) := by
  have h : wordRep n d (e'.trans e.symm) (positionProduct e' v w) =
      positionProduct e v w := by
    ext x
    change v (fun i => x ((e'.trans e.symm) (e'.symm (Sum.inl i)))) *
      w (fun i => x ((e'.trans e.symm) (e'.symm (Sum.inr i)))) = _
    
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
    rfl
  rw [← h, cyclic_translate_eq]

lemma restriction_equal_degrees {n a b n' a' b' : ℕ} {α β γ : YoungDiagram}
    (ha : a = a') (hb : b = b') (hn : n = n')
    (ta : Tableau a α) (tb : Tableau b β) (tt : Tableau n γ)
    (e : Fin n ≃ Fin a ⊕ Fin b)
    (F : Representation.IntertwiningMap ((spechtRep tt).comp (sumPermHom e))
      (externalTensor (spechtRep ta) (spechtRep tb))) (hF : F ≠ 0) :
    ∃ (sa : Tableau a' α) (sb : Tableau b' β) (st : Tableau n' γ)
      (e' : Fin n' ≃ Fin a' ⊕ Fin b'),
      ∃ G : Representation.IntertwiningMap ((spechtRep st).comp (sumPermHom e'))
        (externalTensor (spechtRep sa) (spechtRep sb)), G ≠ 0 := by
  subst a'; subst b'; subst n'
  exact ⟨ta,tb,tt,e,F,hF⟩

theorem even_rows_restriction (r D : ℕ) (θ : YoungDiagram) (hθ : θ.card = 2*r)
    (he : ∀ i, Even (θ.rowLen i)) (hd : θ.colLen 0 ≤ 2*D) :
    ∃ (α β : YoungDiagram) (ta : Tableau r α) (tb : Tableau r β)
      (tt : Tableau (2*r) θ) (e : Fin (2*r) ≃ Fin r ⊕ Fin r),
      α.colLen 0 ≤ D ∧ β.colLen 0 ≤ D ∧
      ShortColumns.RowParity (r%2) α ∧ ShortColumns.RowParity (r%2) β ∧
      ∃ F : Representation.IntertwiningMap ((spechtRep tt).comp (sumPermHom e))
        (externalTensor (spechtRep ta) (spechtRep tb)), F ≠ 0 := by
  obtain ⟨ps,ht,hp,ha,hb,hpa,hpb⟩ := Columns.even_rows_allocation r D θ hθ he hd
  let α := Columns.columnShape (ps.map Prod.fst)
  let β := Columns.columnShape (ps.map Prod.snd)
  obtain ⟨ea,hra,hca⟩ := Columns.columnShape_placement (ps.map Prod.fst)
  obtain ⟨eb,hrb,hcb⟩ := Columns.columnShape_placement (ps.map Prod.snd)
  have heθ := Columns.columnShape_placement (ps.map (fun p => p.1+p.2))
  rw [ht] at heθ
  obtain ⟨et,hrt,hct⟩ := heθ
  obtain ⟨F,hF⟩ := FlagColumns.column_split_restriction ps α β θ ea eb et
    hra hrb hrt hca hcb hct D D (fun p h => (hp p h).1) (fun p h => (hp p h).2)
  have hn : (ps.map (fun p => p.1+p.2)).sum = 2*r :=
    (Columns.placed_card et).symm.trans hθ
  obtain ⟨ta,tb,tt,e,G,hG⟩ := restriction_equal_degrees ha hb hn _ _ _ _ F hF
  refine ⟨α,β,ta,tb,tt,e,?_,?_,hpa,hpb,G,hG⟩
  · exact Columns.placed_height ea hra D (by
      intro h hh; obtain ⟨p,hp',rfl⟩ := List.mem_map.mp hh; exact (hp p hp').1)
  · exact Columns.placed_height eb hrb D (by
      intro h hh; obtain ⟨p,hp',rfl⟩ := List.mem_map.mp hh; exact (hp p hp').2)

lemma rowColumnTransposeCyclicMap_surjective {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    Function.Surjective (rowColumnTransposeCyclicMap t) := by
  intro y
  let y' : (cyclic (wordRep n (μ.transpose.colLen 0 * μ.colLen 0))
      (rowColumnTransposeMap t (rowColumnWord (transposeTableau t)))).toSubmodule :=
    ⟨y.val, by simpa only [rowColumnCyclic, rowColumnTransposeMap_word] using y.property⟩
  obtain ⟨x,hx⟩ := cyclicMap_surjective (rowColumnTransposeMap t)
    (rowColumnWord (transposeTableau t)) y'
  have hv : rowColumnTransposeMap t x.val = y.val := congrArg (fun z => z.val) hx
  exact ⟨x, Subtype.ext hv⟩

def rowColumnTransposeCyclicEquiv {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    (rowColumnCyclic (transposeTableau t)).toRepresentation.Equiv
      (rowColumnCyclic t).toRepresentation :=
  (rowColumnTransposeCyclicMap t).ofBijective
    ⟨rowColumnTransposeCyclicMap_injective t, rowColumnTransposeCyclicMap_surjective t⟩

namespace ShortColumns

lemma one_extra_degree (b δ n : ℕ) (hδ : δ ≤ 1) (hn : 2*b+δ = n)
    (s : Tableau n (shape b δ)) (μ : YoungDiagram) (t : Tableau n μ)
    (hp : RowParity δ μ) (hd : μ.colLen 0 ≤ 4) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (signTwist (rowColumnCyclic s).toRepresentation), F ≠ 0 := by
  subst n
  exact one_extra b δ hδ s μ t hp hd

lemma one_extra_lifted (r d : ℕ) (s : Tableau r (shape (r/2) (r%2)))
    (φ : Fin ((shape (r/2) (r%2)).transpose.colLen 0 *
      (shape (r/2) (r%2)).colLen 0) → Fin d) (hφ : Function.Injective φ)
    (μ : YoungDiagram) (t : Tableau r μ) (hp : RowParity (r%2) μ)
    (hd : μ.colLen 0 ≤ 4) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (signTwist (cyclic (wordRep r d) (letterLift φ (rowColumnWord s))).toRepresentation),
      Function.Injective F := by
  obtain ⟨f,hf⟩ := one_extra_degree (r/2) (r%2) r (by omega) (by omega) s μ t hp hd
  let G := signTwistMap (cyclicMap (letterLift φ) (rowColumnWord s))
  have hG : Function.Injective G := cyclicMap_injective _ _ (letterLift_injective φ hφ)
  let := specht_irreducible t
  exact ⟨G.comp f, hG.comp ((Representation.IsIrreducible.injective_or_eq_zero f).resolve_right hf)⟩

theorem two_extras_lifted (r d : ℕ) (s₁ s₂ : Tableau r (shape (r/2) (r%2)))
    (φ ψ : Fin ((shape (r/2) (r%2)).transpose.colLen 0 *
      (shape (r/2) (r%2)).colLen 0) → Fin d)
    (hφ : Function.Injective φ) (hψ : Function.Injective ψ)
    (A : Fin d → Prop) (hA : ∀ x, A (φ x)) (hB : ∀ x, ¬ A (ψ x))
    (e : Fin (2*r) ≃ Fin r ⊕ Fin r)
    (η : YoungDiagram) (hη : η.card = 2*r) (t : Tableau (2*r) η)
    (he : ∀ i, Even (η.colLen i)) (hd : η.rowLen 0 ≤ 8) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep (2*r) d) (positionProduct e
        (letterLift φ (rowColumnWord s₁)) (letterLift ψ (rowColumnWord s₂)))).toRepresentation,
      F ≠ 0 := by
  obtain ⟨α,β,ta,tb,tt,e₀,ha,hb,hpa,hpb,f,hf⟩ :=
    even_rows_restriction r 4 η.transpose (by rwa [transpose_card])
      (by simpa only [YoungDiagram.rowLen_transpose] using he)
      (by simpa only [YoungDiagram.colLen_transpose] using hd)
  obtain ⟨Fa,hFa⟩ := one_extra_lifted r d s₁ φ hφ α ta hpa ha
  obtain ⟨Fb,hFb⟩ := one_extra_lifted r d s₂ ψ hψ β tb hpb hb
  have hs := signed_external_cyclic_support (spechtRep tt) (spechtRep ta) (spechtRep tb)
    e₀ (letterLift φ (rowColumnWord s₁)) (letterLift ψ (rowColumnWord s₂)) A
    (letterLift_mem_alphabet A φ hA _) (letterLift_mem_alphabet (fun x => ¬ A x) ψ hB _)
    Fa Fb hFa hFb f hf
  rw [cyclic_positionProduct_eq e₀ e] at hs
  obtain ⟨H,hH⟩ := hs
  have hEq := specht_sign_transpose t
  change Nonempty ((spechtRep t).Equiv
    (signTwist (spechtSub (transposeTableau t)).toRepresentation)) at hEq
  rw [spechtSub_tableau_independent (transposeTableau t) tt] at hEq
  obtain ⟨E⟩ := hEq
  refine ⟨H.comp E.toIntertwiningMap, ?_⟩
  intro hz
  apply hH
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  obtain ⟨y,rfl⟩ := E.surjective x
  exact congrArg (fun K => K y) hz

lemma one_extra_transpose_lifted (r d : ℕ) (s : Tableau r (shape (r/2) (r%2)))
    (φ : Fin ((shape (r/2) (r%2)).transpose.transpose.colLen 0 *
      (shape (r/2) (r%2)).transpose.colLen 0) → Fin d) (hφ : Function.Injective φ)
    (μ : YoungDiagram) (t : Tableau r μ) (hp : RowParity (r%2) μ)
    (hd : μ.colLen 0 ≤ 4) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (signTwist (cyclic (wordRep r d)
        (letterLift φ (rowColumnWord (transposeTableau s)))).toRepresentation),
      Function.Injective F := by
  obtain ⟨f,hf⟩ := one_extra_degree (r/2) (r%2) r (by omega) (by omega) s μ t hp hd
  let E := (rowColumnTransposeCyclicEquiv s).symm
  let G := signTwistMap ((cyclicMap (letterLift φ) (rowColumnWord (transposeTableau s))).comp
    E.toIntertwiningMap)
  have hG : Function.Injective G :=
    (cyclicMap_injective _ _ (letterLift_injective φ hφ)).comp E.injective
  let := specht_irreducible t
  exact ⟨G.comp f, hG.comp ((Representation.IsIrreducible.injective_or_eq_zero f).resolve_right hf)⟩

theorem two_extras (r d : ℕ) (s₁ s₂ : Tableau r (shape (r/2) (r%2)))
    (φ : Fin ((shape (r/2) (r%2)).transpose.colLen 0 *
      (shape (r/2) (r%2)).colLen 0) → Fin d)
    (ψ : Fin ((shape (r/2) (r%2)).transpose.transpose.colLen 0 *
      (shape (r/2) (r%2)).transpose.colLen 0) → Fin d)
    (hφ : Function.Injective φ) (hψ : Function.Injective ψ)
    (A : Fin d → Prop) (hA : ∀ x, A (φ x)) (hB : ∀ x, ¬ A (ψ x))
    (e : Fin (2*r) ≃ Fin r ⊕ Fin r)
    (η : YoungDiagram) (hη : η.card = 2*r) (t : Tableau (2*r) η)
    (he : ∀ i, Even (η.colLen i)) (hd : η.rowLen 0 ≤ 8) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep (2*r) d) (positionProduct e
        (letterLift φ (rowColumnWord s₁))
        (letterLift ψ (rowColumnWord (transposeTableau s₂))))).toRepresentation,
      F ≠ 0 := by
  obtain ⟨α,β,ta,tb,tt,e₀,ha,hb,hpa,hpb,f,hf⟩ :=
    even_rows_restriction r 4 η.transpose (by rwa [transpose_card])
      (by simpa only [YoungDiagram.rowLen_transpose] using he)
      (by simpa only [YoungDiagram.colLen_transpose] using hd)
  obtain ⟨Fa,hFa⟩ := one_extra_lifted r d s₁ φ hφ α ta hpa ha
  obtain ⟨Fb,hFb⟩ := one_extra_transpose_lifted r d s₂ ψ hψ β tb hpb hb
  have hs := signed_external_cyclic_support (spechtRep tt) (spechtRep ta) (spechtRep tb)
    e₀ (letterLift φ (rowColumnWord s₁)) (letterLift ψ (rowColumnWord (transposeTableau s₂))) A
    (letterLift_mem_alphabet A φ hA _) (letterLift_mem_alphabet (fun x => ¬ A x) ψ hB _)
    Fa Fb hFa hFb f hf
  rw [cyclic_positionProduct_eq e₀ e] at hs
  obtain ⟨H,hH⟩ := hs
  have hEq := specht_sign_transpose t
  change Nonempty ((spechtRep t).Equiv
    (signTwist (spechtSub (transposeTableau t)).toRepresentation)) at hEq
  rw [spechtSub_tableau_independent (transposeTableau t) tt] at hEq
  obtain ⟨E⟩ := hEq
  refine ⟨H.comp E.toIntertwiningMap, ?_⟩
  intro hz
  apply hH
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  obtain ⟨y,rfl⟩ := E.surjective x
  exact congrArg (fun K => K y) hz

end ShortColumns
end Saxl
end
end

end OAI
