import OAI.Topology.ArtinGroups.ParabolicIntersections.StandardEmbedding
import OAI.Topology.ArtinGroups.ParabolicIntersections.ArtinRelabel
import OAI.Topology.ArtinGroups.ParabolicIntersections.RelativeInitialStabilizer

namespace OAI

/-! Discharge of the one-color standard embedding input. -/
namespace HarmonicArtin.ParabolicIntersections
open CoxeterExchange
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (X : Set S)

omit [LinearOrder S] in
/-- The relative extension includes the original Artin presentation injectively. -/
theorem relative_embedding_input : VanDerLekRelativeEmbedding M X := by
  let N := relativeMatrix M X
  let T : Set (S⊕Unit) := Set.range Sum.inl
  let e : S ≃ T := Equiv.ofInjective (Sum.inl : S → S⊕Unit) Sum.inl_injective
  let R := restrictedMatrix N T
  have hu : ∀ i j : S, R (e i) (e j)=M i j := fun _ _ => rfl
  have hd : ∀ i j : T, M (e.symm i) (e.symm j)=R i j := by
    intro i j
    have hi : Sum.inl (e.symm i)=i.val := congrArg Subtype.val (e.apply_symm_apply i)
    have hj : Sum.inl (e.symm j)=j.val := congrArg Subtype.val (e.apply_symm_apply j)
    change M (e.symm i) (e.symm j)=N i.val j.val
    rw [←hi,←hj]
    rfl
  let up := artinMap M R e hu
  have hup : Function.Injective up := (artinMap_leftInverse M R e hu e.symm hd e.left_inv).injective
  have hfactor : (restrictedArtinHom N T).comp up=relativeArtinHom M X := by
    apply PresentedGroup.ext
    intro s
    change restrictedArtinHom N T (artinMap M R e hu (generator M s)) =
      relativeArtinHom M X (generator M s)
    rw [artinMap_generator,restrictedArtinHom_generator,relativeArtinHom_generator]
    rfl
  refine ⟨?_⟩
  rw [←hfactor]
  exact (standardArtinEmbedding N T).comp hup

end HarmonicArtin.ParabolicIntersections

end OAI
