import Mathlib
import OAI.Topology.ArtinGroups.Quivers.OrthogonalVertices
import OAI.Topology.ArtinGroups.Quivers.PacketIndex

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I J L : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

noncomputable def packetConsEquiv (E : BasedComplex Q (K := K) I)
    (α:V) (v:J → V) (h : ∀ a, OrthogonalVertices Q α (v a)) :
    (PacketIndex Q E.placement (fun z : Option J => z.elim α v) ⊕ I) ≃
      (TestIndex Q (E.packetTwist Q v).placement α ⊕ (PacketIndex Q E.placement v ⊕ I)) where
  toFun
    | .inl ⟨none,u⟩ => .inl ⟨.inr u.1,u.2⟩
    | .inl ⟨some a,u⟩ => .inr (.inl ⟨a,u⟩)
    | .inr i => .inr (.inr i)
  invFun
    | .inl ⟨.inl ⟨a,_⟩,p⟩ => (no_corner_of_orthogonal Q (h a) p).elim
    | .inl ⟨.inr i,p⟩ => .inl ⟨none,i,p⟩
    | .inr (.inl ⟨a,u⟩) => .inl ⟨some a,u⟩
    | .inr (.inr i) => .inr i
  left_inv z := by rcases z with ⟨_|a,u⟩|i <;> rfl
  right_inv z := by
    rcases z with ⟨⟨a,x⟩|i,p⟩|⟨a,u⟩|i
    · exact (no_corner_of_orthogonal Q (h a) p).elim
    all_goals rfl

lemma packetCons_eq (E : BasedComplex Q (K := K) I)
    (α:V) (v:J → V) (h : ∀ a, OrthogonalVertices Q α (v a)) :
    ((E.packetTwist Q v).positiveTwist Q α).reindex Q (packetConsEquiv Q E α v h) =
      E.packetTwist Q (fun z : Option J => z.elim α v) := by
  apply ext_placement_differential Q
  · funext z
    rcases z with ⟨_|a,u⟩|i <;> rfl
  · apply Matrix.ext
    intro z w
    rcases z with ⟨_|a,u⟩|i <;> rcases w with ⟨_|b,t⟩|j
    all_goals dsimp only [reindex, Matrix.submatrix_apply, packetConsEquiv, Equiv.coe_fn_mk]
    all_goals simp only [
      positiveTwist_differential,packetTwist,Map.cone,packetEvaluation,packetTest,
      Map.coneDifferential,Matrix.fromBlocks,Matrix.of_apply,Matrix.neg_apply,Matrix.zero_apply,
      testTransform,scalarCornerMatrix,testMatrix,packetDifferential,packetEvaluationMatrix,
      evaluationMatrix,Sum.inr_ne_inl,Sum.inr.injEq,Sum.elim_inl,Sum.elim_inr,Option.elim_none,
      Option.elim_some,Matrix.blockDiagonal'_apply_eq,↓reduceIte]
    · rw [Matrix.blockDiagonal'_apply_ne _ _ _ (by simp),neg_zero]
    · rw [Matrix.blockDiagonal'_apply_ne _ _ _ (by simp),neg_zero]
    · by_cases hab : a=b
      · subst b
        simp only [Matrix.blockDiagonal',Matrix.of_apply, ↓reduceDIte,Option.elim_some]
      · simp only [Matrix.blockDiagonal',Matrix.of_apply,hab,Option.some.injEq, ↓reduceDIte]

variable [Fintype L] [DecidableEq L]

def packetReindexEquiv (E : BasedComplex Q (K := K) I) (v:J → V) (e:L ≃ J) :
    (PacketIndex Q E.placement (v ∘ e) ⊕ I) ≃ (PacketIndex Q E.placement v ⊕ I) :=
  Equiv.sumCongr (Equiv.sigmaCongrLeft (β := fun a : J => TestIndex Q E.placement (v a)) e) (Equiv.refl I)

omit [DecidableEq I] in
lemma packetReindex_eq (E : BasedComplex Q (K := K) I) (v:J → V) (e:L ≃ J) :
    (E.packetTwist Q v).reindex Q (packetReindexEquiv Q E v e) = E.packetTwist Q (v ∘ e) := by
  apply ext_placement_differential Q
  · funext z
    rcases z with ⟨a,u⟩|i <;> rfl
  · apply Matrix.ext
    intro z w
    rcases z with ⟨a,u⟩|i <;> rcases w with ⟨b,t⟩|j
    · change -(Matrix.blockDiagonal' (fun a => scalarCornerMatrix Q (v a)
        (testMatrix Q E.placement E.placement (v a) E.differential)) ⟨e a,u⟩ ⟨e b,t⟩) = _
      by_cases hab : a=b
      · subst b
        simp only [packetTwist,Map.cone,Map.coneDifferential,packetEvaluation,packetTest,
          packetDifferential,Matrix.fromBlocks,Matrix.of_apply,Matrix.neg_apply,
          Matrix.blockDiagonal'_apply_eq,Function.comp_apply,Sum.elim_inl]
      · rw [Matrix.blockDiagonal'_apply_ne _ _ _ (fun he => hab (e.injective he))]
        change -(0 : Zigzag Q K) = -(Matrix.blockDiagonal' (fun a : L =>
          scalarCornerMatrix Q (v (e a)) (testMatrix Q E.placement E.placement (v (e a)) E.differential)) ⟨a,u⟩ ⟨b,t⟩)
        rw [Matrix.blockDiagonal'_apply_ne _ _ _ hab]
    all_goals rfl

def packetEmptyEquiv (E : BasedComplex Q (K := K) I) (v:J → V) [IsEmpty J] :
    I ≃ (PacketIndex Q E.placement v ⊕ I) where
  toFun := Sum.inr
  invFun z := z.elim (fun a => isEmptyElim a.1) id
  left_inv _ := rfl
  right_inv z := by
    rcases z with z|i
    · exact isEmptyElim z.1
    · rfl

omit [DecidableEq I] in
lemma packetEmpty_eq (E : BasedComplex Q (K := K) I) (v:J → V) [IsEmpty J] :
    (E.packetTwist Q v).reindex Q (packetEmptyEquiv Q E v) = E := by
  apply ext_placement_differential Q <;> rfl

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
