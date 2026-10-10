import OAI.RepresentationTheory.YoungSymmetry.Dimensions
import OAI.RepresentationTheory.FiniteUnitary.Action
import OAI.RepresentationTheory.FiniteUnitary.KernelBounds

namespace OAI

namespace CubeShuffle.Specht
open scoped BigOperators Classical

noncomputable def spaceHilbertEquiv (μ : YoungDiagram) : space μ ≃ₗ[ℂ] hilbertSpace μ :=
  (hilbertEquiv μ).submoduleMap (space μ)

noncomputable def unitaryRepresentation (μ : YoungDiagram) :
    Representation ℂ (Equiv.Perm (Cell μ)) (hilbertSpace μ) :=
  ((spaceHilbertEquiv μ).conjAlgEquiv ℂ).toMonoidHom.comp (representation μ)

lemma unitaryRepresentation_coe (μ : YoungDiagram) (p : Equiv.Perm (Cell μ))
    (v : hilbertSpace μ) :
    (unitaryRepresentation μ p v : PermutationHilbert.H (Tabloid μ)) =
      PermutationHilbert.act (tabloidAct p) v := by
  obtain ⟨w,rfl⟩ := (spaceHilbertEquiv μ).surjective v
  change hilbertEquiv μ (tabloidRep μ p w) = _
  exact hilbert_action μ p w

noncomputable def unitaryEquiv (μ : YoungDiagram) :
    Representation.Equiv (representation μ) (unitaryRepresentation μ) :=
  Representation.Equiv.mk (spaceHilbertEquiv μ) (by
    intro p
    apply LinearMap.ext
    intro v
    change spaceHilbertEquiv μ (representation μ p v) =
      spaceHilbertEquiv μ (representation μ p ((spaceHilbertEquiv μ).symm (spaceHilbertEquiv μ v)))
    rw [LinearEquiv.symm_apply_apply])

lemma unitaryRepresentation_irreducible (μ : YoungDiagram) :
    Representation.IsIrreducible (unitaryRepresentation μ) := by
  let := representation_irreducible μ
  exact UnitaryFinite.irreducible_of_equiv _ _ (unitaryEquiv μ)

lemma unitaryRepresentation_unitary (μ : YoungDiagram) :
    UnitaryFinite.IsUnitary (G := Equiv.Perm (Cell μ)) (V := hilbertSpace μ) (unitaryRepresentation μ) := by
  intro p v w
  change inner ℂ (unitaryRepresentation μ p v : PermutationHilbert.H (Tabloid μ))
      (unitaryRepresentation μ p w : PermutationHilbert.H (Tabloid μ)) = _
  rw [unitaryRepresentation_coe,unitaryRepresentation_coe]
  exact (PermutationHilbert.act (tabloidAct p)).inner_map_map v w

end CubeShuffle.Specht
namespace CubeShuffle.Specht
open scoped BigOperators Classical

noncomputable def tupleFixedEquiv (μ : YoungDiagram) {ι : Type*} [Fintype ι]
    (e : ι ↪ Cell μ) :
    UnitaryFinite.fixedSpace (V := hilbertSpace μ) UnitaryFinite.tupleAction e (unitaryRepresentation μ) ≃ₗ[ℂ]
      fixedHilbert μ (Finset.univ.image e) where
  toFun v := ⟨v.1.1,v.1.2,by
    intro p hp
    have h := v.2 p ((UnitaryFinite.tupleAction_fixed_iff e p).mpr hp)
    exact (unitaryRepresentation_coe μ p v.1).symm.trans (congrArg Subtype.val h)⟩
  invFun v := ⟨⟨v.1,v.2.1⟩,by
    intro p hp
    apply Subtype.ext
    exact (unitaryRepresentation_coe μ p _).trans
      (v.2.2 p ((UnitaryFinite.tupleAction_fixed_iff e p).mp hp))⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- True near-row multiplicity lower bound in the actual ordered-tuple action. -/
theorem tupleFixed_dimension (μ : YoungDiagram) {ι : Type*} [Fintype ι]
    (e : ι ↪ Cell μ) :
    Module.finrank ℂ (hilbertSpace μ) * (Fintype.card ι).choose (μ.card-μ.rowLen 0) ≤
      Module.finrank ℂ (UnitaryFinite.fixedSpace (V := hilbertSpace μ) UnitaryFinite.tupleAction e (unitaryRepresentation μ)) *
        μ.card.choose (μ.card-μ.rowLen 0) := by
  rw [(tupleFixedEquiv μ e).finrank_eq,finrank_hilbertSpace]
  have h := fixedHilbert_dimension μ (Finset.univ.image e)
  simpa only [Finset.card_image_of_injective _ e.injective,Finset.card_univ] using h

end CubeShuffle.Specht

namespace CubeShuffle.Specht
open scoped BigOperators Classical

variable {α ι : Type*} [Fintype α] [Fintype ι]

noncomputable def relabelledUnitary (μ : YoungDiagram) (e : α ≃ Cell μ) :
    Representation ℂ (Equiv.Perm α) (hilbertSpace μ) :=
  (unitaryRepresentation μ).comp e.permCongrHom.toMonoidHom

omit [Fintype α] in
lemma relabelledUnitary_unitary (μ : YoungDiagram) (e : α ≃ Cell μ) :
    UnitaryFinite.IsUnitary (V := hilbertSpace μ) (relabelledUnitary μ e) := by
  intro g v w
  exact unitaryRepresentation_unitary μ (e.permCongr g) v w

omit [Fintype α] in
lemma relabelledUnitary_irreducible (μ : YoungDiagram) (e : α ≃ Cell μ) :
    Representation.IsIrreducible (relabelledUnitary μ e) := by
  let := unitaryRepresentation_irreducible μ
  exact UnitaryFinite.irreducible_comp_equiv (V := hilbertSpace μ) (unitaryRepresentation μ) e.permCongrHom

noncomputable def relabelledTupleFixed (μ : YoungDiagram) (e : α ≃ Cell μ) (f : ι ↪ α) :
    UnitaryFinite.fixedSpace (V := hilbertSpace μ) UnitaryFinite.tupleAction f (relabelledUnitary μ e) ≃ₗ[ℂ]
    UnitaryFinite.fixedSpace (V := hilbertSpace μ) UnitaryFinite.tupleAction (f.trans e.toEmbedding) (unitaryRepresentation μ) where
  toFun v := ⟨v.1,by
    intro g hg
    have hp : UnitaryFinite.tupleAction (e.symm.permCongr g) f=f := by
      apply Function.Embedding.ext
      intro i
      have hh := congrArg (fun f : ι ↪ Cell μ => f i) hg
      change g (e (f i))=e (f i) at hh
      simp only [UnitaryFinite.tupleAction_apply,Equiv.permCongr_apply,Equiv.symm_symm,e.symm_apply_apply,hh]
    have hh := v.2 (e.symm.permCongr g) hp
    change unitaryRepresentation μ (e.permCongr (e.symm.permCongr g)) v=v at hh
    have he : e.permCongr (e.symm.permCongr g)=g := by
      apply Equiv.ext
      intro x
      simp only [Equiv.permCongr_apply,Equiv.symm_symm,e.apply_symm_apply]
    simpa only [he] using hh⟩
  invFun v := ⟨v.1,by
    intro g hg
    have hp : UnitaryFinite.tupleAction (e.permCongr g) (f.trans e.toEmbedding)=f.trans e.toEmbedding := by
      apply Function.Embedding.ext
      intro i
      have hh := congrArg (fun f : ι ↪ α => f i) hg
      change g (f i)=f i at hh
      simp only [UnitaryFinite.tupleAction_apply,Function.Embedding.trans_apply,
        Equiv.toEmbedding_apply,Equiv.permCongr_apply,e.symm_apply_apply,hh]
    exact v.2 (e.permCongr g) hp⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype α] in
lemma relabelled_tuple_dimension (μ : YoungDiagram) (e : α ≃ Cell μ) (f : ι ↪ α) :
    Module.finrank ℂ (hilbertSpace μ) * (Fintype.card ι).choose (μ.card-μ.rowLen 0) ≤
      Module.finrank ℂ (UnitaryFinite.fixedSpace (V := hilbertSpace μ) UnitaryFinite.tupleAction f (relabelledUnitary μ e)) *
        μ.card.choose (μ.card-μ.rowLen 0) := by
  rw [(relabelledTupleFixed μ e f).finrank_eq]
  exact tupleFixed_dimension μ (f.trans e.toEmbedding)

end CubeShuffle.Specht

end OAI
