import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Specht.CountedPieri

namespace OAI

/-! Counted Gluing. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

lemma wordContent_equiv {n d : ℕ} {w z : Fin n → Fin d}
    (h : ∀ j, wordContent w j = wordContent z j) :
    ∃ q : Equiv.Perm (Fin n), z ∘ q = w := by
  classical
  let f (j : Fin d) : {i : Fin n // w i = j} ≃ {i : Fin n // z i = j} :=
    Fintype.equivOfCardEq (by simpa only [Fintype.card_subtype,wordContent] using h j)
  let q := (Equiv.sigmaFiberEquiv w).symm.trans
    ((Equiv.sigmaCongrRight f).trans (Equiv.sigmaFiberEquiv z))
  exact ⟨q,funext (fun i => (f (w i) ⟨i,rfl⟩).property)⟩

lemma cyclic_wordContent {n d : ℕ} {w z : Fin n → Fin d}
    (h : ∀ j, wordContent w j = wordContent z j) :
    cyclic (wordRep n d) (Pi.single w 1) = cyclic (wordRep n d) (Pi.single z 1) := by
  obtain ⟨q,hq⟩ := wordContent_equiv h
  have he : wordRep n d q⁻¹ (Pi.single z 1) = Pi.single w 1 := by
    rw [wordRep_single,inv_inv,hq]
  rw [← he,cyclic_action_eq]

lemma coind_outer_map {G H K L X Y W : Type*}
    [Group G] [Group H] [Group K] [Group L]
    [Fintype G] [Fintype H] [DecidableEq G] [DecidableEq H]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (G × H) W)
    (φ : K →* G) (ψ : L →* H)
    (σ : Representation ℂ K X) (τ : Representation ℂ L Y)
    (J : Representation.IntertwiningMap ρ
      (outer (Representation.coind φ σ) (Representation.coind ψ τ))) (hJ : J ≠ 0) :
    ∃ F : Representation.IntertwiningMap ρ
      (Representation.coind (φ.prodMap ψ) (outer σ τ)), F ≠ 0 := by
  refine ⟨(coindOuter φ ψ σ τ).comp J, ?_⟩
  intro h
  apply hJ
  ext x
  have hx := congrArg (fun f => (f : Representation.IntertwiningMap ρ
    (Representation.coind (φ.prodMap ψ) (outer σ τ))) x) h
  apply coindOuter_injective φ ψ σ τ
  exact hx.trans (map_zero (coindOuter φ ψ σ τ)).symm

lemma coind_composed_map {G H K X W : Type*}
    [Group G] [Group H] [Group K]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G W) (φ : K →* H) (ψ : H →* G)
    (σ : Representation ℂ K X)
    (J : Representation.IntertwiningMap (ρ.comp ψ) (Representation.coind φ σ))
    (hJ : J ≠ 0) :
    ∃ F : Representation.IntertwiningMap ρ (Representation.coind (ψ.comp φ) σ), F ≠ 0 := by
  let V := coindLift ψ J
  have hV : V ≠ 0 := coindLift_ne_zero ψ J hJ
  let Z := coindTrans φ ψ σ
  refine ⟨Z.comp V, ?_⟩
  intro hz
  apply hV
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  apply coindTrans_injective φ ψ σ
  have hx := congrArg (fun f => f x) hz
  exact hx.trans (map_zero Z).symm

theorem coind_product_map {n a b : ℕ} {G H X Y W : Type*}
    [Group G] [Group H]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) W)
    (e : Fin n ≃ Fin a ⊕ Fin b)
    (φ : G →* Equiv.Perm (Fin a)) (ψ : H →* Equiv.Perm (Fin b))
    (σ : Representation ℂ G X) (τ : Representation ℂ H Y)
    (J : Representation.IntertwiningMap (ρ.comp (sumPermHom e))
      (outer (Representation.coind φ σ) (Representation.coind ψ τ))) (hJ : J ≠ 0) :
    ∃ F : Representation.IntertwiningMap ρ
      (Representation.coind ((sumPermHom e).comp (φ.prodMap ψ)) (outer σ τ)), F ≠ 0 := by
  obtain ⟨U,hU⟩ := coind_outer_map (ρ.comp (sumPermHom e)) φ ψ σ τ J hJ
  let : AddCommGroup (X ⊗[ℂ] Y) := Module.addCommMonoidToAddCommGroup ℂ
  exact coind_composed_map ρ (φ.prodMap ψ) (sumPermHom e) (outer σ τ) U hU

theorem outer_coind_map {n a b : ℕ} {G H X Y Z W : Type*}
    [Group G] [Group H]
    [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X]
    [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup Z] [Module ℂ Z] [FiniteDimensional ℂ Z]
    [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) W)
    (e : Fin n ≃ Fin a ⊕ Fin b)
    (φ : G →* Equiv.Perm (Fin a)) (ψ : H →* Equiv.Perm (Fin b))
    (σ : Representation ℂ G X) (τ : Representation ℂ H Y)
    (ζ : Representation ℂ (Equiv.Perm (Fin b)) Z)
    (L : Representation.IntertwiningMap (ρ.comp (sumPermHom e))
      (outer (Representation.coind φ σ) ζ)) (hL : L ≠ 0)
    (hQ : SupportLE ζ (Representation.coind ψ τ)) :
    ∃ F : Representation.IntertwiningMap ρ
      (Representation.coind ((sumPermHom e).comp (φ.prodMap ψ)) (outer σ τ)), F ≠ 0 := by
  have hh := (SupportLE.refl (Representation.coind φ σ)).outer hQ
  obtain ⟨J,hJ⟩ := hh.detects_map L hL
  exact coind_product_map ρ e φ ψ σ τ J hJ

theorem stripChain_coind_map {n a b : ℕ} {ν μ : YoungDiagram} {bs : List ℕ}
    {G H X Y : Type*} [Group G] [Group H]
    [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X]
    [AddCommGroup Y] [Module ℂ Y]
    (hs : SizedStripChain bs ν μ) (s : Tableau a ν) (t : Tableau n μ)
    (e : Fin n ≃ Fin a ⊕ Fin b)
    (φ : G →* Equiv.Perm (Fin a)) (ψ : H →* Equiv.Perm (Fin b))
    (σ : Representation ℂ G X) (τ : Representation ℂ H Y)
    (K : Representation.IntertwiningMap (spechtRep s) (Representation.coind φ σ))
    (hK : K ≠ 0) (w : Fin b → Fin bs.length)
    (hw : ∀ j, wordContent w j = bs.get j)
    (hQ : SupportLE (cyclic (wordRep b bs.length) (Pi.single w 1)).toRepresentation
      (Representation.coind ψ τ)) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (Representation.coind ((sumPermHom e).comp (φ.prodMap ψ)) (outer σ τ)), F ≠ 0 := by
  classical
  obtain ⟨c,hc,hLL⟩ := stripChain_outer_map hs s t e (Representation.coind φ σ) K hK
  have he := cyclic_wordContent (fun j => (hc j).trans (hw j).symm)
  rw [he] at hLL
  obtain ⟨L,hL⟩ := hLL
  let := specht_irreducible t
  exact outer_coind_map (spechtRep t) e φ ψ σ τ
    (cyclic (wordRep b bs.length) (Pi.single w 1)).toRepresentation L hL hQ

lemma single_coindLift_injective {n : ℕ} {Y : Type*}
    [AddCommGroup Y] [Module ℂ Y]
    (σ : Representation ℂ (Equiv.Perm (Fin n)) Y) (k : ℕ) :
    Function.Injective (coindLift
      ((fiberGroup (fun _ : Fin n => k)).subtype.comp (Balance.singleFiberHom n k))
      (Representation.IntertwiningMap.id σ)) := by
  intro x y he
  have hh := congrArg (fun z => z.val 1) he
  change σ 1 x = σ 1 y at hh
  simpa only [map_one,Module.End.one_apply] using hh

namespace Balance

theorem Piece.kronecker_pos_of_map {n : ℕ} {G Y : Type*}
    [Group G] [Finite G] [AddCommGroup Y] [Module ℂ Y]
    {lam μ : YoungDiagram} (a : Tableau n lam) (t : Tableau n μ)
    {c : Fin n → ℕ} {A : Fin (lam.colLen 0 * lam.colLen 0) → Prop}
    {label : Fin (lam.colLen 0 * lam.colLen 0) → ℕ} {σ : ℕ → ℤ}
    {φ : G →* fiberGroup c} {τ : Representation ℂ G Y}
    (P : Piece (polytabloid a) c A label σ φ τ)
    (ho : ∀ a b, A a → A b → label a < label b → output a < output b)
    (F : Representation.IntertwiningMap (spechtRep t)
      (Representation.coind ((fiberGroup c).subtype.comp φ) τ)) (hF : F ≠ 0) :
    0 < kronecker a a t := by
  have hs := P.support ho (spechtRep t) F hF
  rw [cyclicSquareMap_polytabloid] at hs
  obtain ⟨T,hT⟩ := hs
  let : AddCommGroup (Specht a ⊗[ℂ] Specht a) := Module.addCommMonoidToAddCommGroup ℂ
  obtain ⟨E,hE⟩ := subrepresentation_embeds_of_le_range (spechtTensorMap a a)
    (spechtTensorMap a a).range le_rfl
  exact (kronecker_pos_iff a a t).mpr ⟨E.comp T,intertwining_comp_ne_zero E hE T hT⟩

end Balance
end Saxl
end
end

end OAI
