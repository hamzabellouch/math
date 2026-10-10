import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Balance.BalancedPairs
import OAI.RepresentationTheory.UniversalSquare.Band.TwoStrip
import OAI.RepresentationTheory.UniversalSquare.Band.TwoPathGeometry

namespace OAI

/-! Pieri Induction. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

theorem horizontal_placed_restriction {n a b : ℕ} {ν μ : YoungDiagram}
    (hs : HorizontalStrip ν μ) (s : Tableau a ν) (t : Tableau n μ)
    (e : Fin n ≃ Fin a ⊕ Fin b) :
    ∃ F : Specht t →ₗ[ℂ] Specht s, Function.Surjective F ∧
      ∀ (h : Equiv.Perm (Fin a)) (q : Equiv.Perm (Fin b)) (x : Specht t),
        F (spechtRep t (sumPerm e h q) x) = spechtRep s h (F x) := by
  obtain ⟨c,F,hF,he⟩ := placed_strip_restriction
    (SizedStripChain.of_horizontal hs) s t e
  exact ⟨F,hF,fun h q => he h q (by funext i; apply Fin.ext; change (c (q i)).val = (c i).val; have h₁ := (c (q i)).isLt; have h₂ := (c i).isLt; simp only [List.length_singleton] at h₁ h₂; omega)⟩

def tensorTrivial {V : Type*} [AddCommGroup V] [Module ℂ V] (b : ℕ) :
    V →ₗ[ℂ] V ⊗[ℂ] WordSpace b 1 :=
  (TensorProduct.mk ℂ V (WordSpace b 1)).flip (fun _ => 1)

lemma tensorTrivial_injective {V : Type*} [AddCommGroup V] [Module ℂ V] (b : ℕ) :
    Function.Injective (tensorTrivial (V := V) b) := by
  intro x y h
  have he := congrArg (rightSlice (LinearMap.proj (fun _ : Fin b => (0 : Fin 1)))) h
  simpa only [tensorTrivial,LinearMap.flip_apply,TensorProduct.mk_apply,
    rightSlice_tmul,LinearMap.proj_apply,one_smul] using he

theorem horizontal_coind_map {n a b : ℕ} {ν μ : YoungDiagram}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (hs : HorizontalStrip ν μ) (s : Tableau a ν) (t : Tableau n μ)
    (e : Fin n ≃ Fin a ⊕ Fin b)
    (σ : Representation ℂ (Equiv.Perm (Fin a)) V)
    (K : Representation.IntertwiningMap (spechtRep s) σ) (hK : K ≠ 0) :
    ∃ F : Representation.IntertwiningMap ((spechtRep t).comp (sumPermHom e))
      (outer σ (wordRep b 1)), F ≠ 0 := by
  obtain ⟨F,hF,hFe⟩ := horizontal_placed_restriction hs s t e
  let L : Representation.IntertwiningMap ((spechtRep t).comp (sumPermHom e))
      (outer σ (wordRep b 1)) := {
    toLinearMap := (tensorTrivial b).comp (K.toLinearMap.comp F)
    isIntertwining' g := by
      apply LinearMap.ext
      intro x
      change K (F (spechtRep t (sumPerm e g.1 g.2) x)) ⊗ₜ[ℂ] (fun _ => 1) =
        (σ g.1 (K (F x))) ⊗ₜ[ℂ] wordRep b 1 g.2 (fun _ => 1)
      rw [hFe,K.isIntertwining]
      rfl }
  refine ⟨L,?_⟩
  intro hz
  apply hK
  ext x
  obtain ⟨y,rfl⟩ := hF x
  apply tensorTrivial_injective b
  have he := congrArg (fun Q : Representation.IntertwiningMap
    ((spechtRep t).comp (sumPermHom e)) (outer σ (wordRep b 1)) => Q y) hz
  change tensorTrivial b (K (F y)) = 0 at he
  change tensorTrivial b (K (F y)) = tensorTrivial b 0
  simpa only [map_zero] using he

namespace Balance

theorem even_twos_odd_coind (m x : ℕ) (hm : 1 ≤ m) (hx : Odd x)
    (hxc : x ≤ 2*m) (a : Tableau (2*m) (ShortColumns.shape m 0))
    (e : Fin (2*m+x) ≃ Fin (2*m) ⊕ Fin x) :
    SupportLE (wordRep (2*m+x) 2)
      (Representation.coind (sumPermHom e)
        (outer (projectedSpechtTensor a a (inOutputs {2})
          (inOutputs_invariant {2})).toRepresentation (wordRep x 1))) := by
  let W := projectedSpechtTensor a a (inOutputs {2}) (inOutputs_invariant {2})
  let : AddCommGroup (W.toSubmodule ⊗[ℂ] WordSpace x 1) :=
    Module.addCommMonoidToAddCommGroup ℂ
  apply word_coind_supportLE
  intro μ t hμ
  have hsize : μ.card = 2*m+x := by
    simpa only [Fintype.card_fin,Fintype.card_coe] using (Fintype.card_congr t).symm
  obtain ⟨ν,hν,hheight,hev,hs⟩ := odd_strip_precursor (2*m) x
    (by exact even_two_mul m) hx hxc μ hsize hμ
  let s := canonicalTableau ν hν
  obtain ⟨K,hK⟩ := repeated_twos m hm a a ν s hev hheight
  have hn : K ≠ 0 := by
    intro hz
    have hp := hK (show K ⟨polytabloid s,mem_cyclic _ _⟩ = K 0 by rw [hz]; rfl)
    exact polytabloid_ne_zero s (congrArg Subtype.val hp)
  exact horizontal_coind_map hs s t e _ K hn

theorem two_paths_two_coind (q : ℕ) (hq : 3 ≤ q)
    (a : Tableau (2*q+2) (ShortColumns.shape q 2).transpose)
    (e : Fin (2*q+4) ≃ Fin (2*q+2) ⊕ Fin 2) :
    SupportLE (wordRep (2*q+4) 4)
      (Representation.coind (sumPermHom e)
        (outer (projectedSpechtTensor a a (inOutputs (Set.Icc q (2*q+3)))
          (inOutputs_invariant (Set.Icc q (2*q+3)))).toRepresentation (wordRep 2 1))) := by
  let W := projectedSpechtTensor a a (inOutputs (Set.Icc q (2*q+3)))
    (inOutputs_invariant (Set.Icc q (2*q+3)))
  let : AddCommGroup (W.toSubmodule ⊗[ℂ] WordSpace 2 1) :=
    Module.addCommMonoidToAddCommGroup ℂ
  apply word_coind_supportLE
  intro μ t hμ
  have hsize : μ.card = 2*q+4 := by
    simpa only [Fintype.card_fin,Fintype.card_coe] using (Fintype.card_congr t).symm
  have hw : 3 ≤ μ.rowLen 0 := by
    have hc := card_of_height_four μ hμ
    have h1 := μ.rowLen_anti 0 1 (by omega)
    have h2 := μ.rowLen_anti 0 2 (by omega)
    have h3 := μ.rowLen_anti 0 3 (by omega)
    omega
  obtain ⟨ν,hcard,hheight,hodd,hs⟩ := horizontal_two_odd_precursor μ hμ hw
  have hν : ν.card = 2*q+2 := by omega
  let s := canonicalTableau ν hν
  obtain ⟨K,hK⟩ := two_paths q a a ν s hheight (by
    obtain ⟨j,hj⟩ := hodd
    exact ⟨j,Nat.odd_iff.mp hj⟩)
  have hn : K ≠ 0 := by
    intro hz
    have hp := hK (show K ⟨polytabloid s,mem_cyclic _ _⟩ = K 0 by rw [hz]; rfl)
    exact polytabloid_ne_zero s (congrArg Subtype.val hp)
  exact horizontal_coind_map hs s t e _ K hn

end Balance
end Saxl
end
end

end OAI
