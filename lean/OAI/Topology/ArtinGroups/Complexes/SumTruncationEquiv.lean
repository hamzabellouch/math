import Mathlib
import OAI.Topology.ArtinGroups.Complexes.SumTestEquiv
import OAI.Topology.ArtinGroups.Complexes.DownClosed

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A K I : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]
  {T : I → Type*} [∀ i, Fintype (T i)] [∀ i, DecidableEq (T i)]
attribute [local instance] Classical.decEq Classical.propDecidable

def sumTruncationEquiv (E : (i:I) → BasedComplex Q (K:=K) (T i)) (d:ℤ) :
    (Σ i,lowerLevelSet Q (E i) d) ≃ lowerLevelSet Q (finiteSum Q E) d where
  toFun x:=⟨⟨x.1,x.2.val⟩,x.2.property⟩
  invFun x:=⟨x.1.1,x.1.2,x.2⟩
  left_inv _:=rfl
  right_inv _:=rfl

omit [Fintype V] [DecidableEq A] [∀ i, DecidableEq (T i)] in
lemma sumTruncation_eq (E : (i:I) → BasedComplex Q (K:=K) (T i))
    (hE:∀ i,(E i).IsMinimal Q) (d:ℤ) :
    (lowerTruncation Q (finiteSum Q E) (finiteSum_minimal Q E hE) d).reindex Q
      (sumTruncationEquiv Q E d)=finiteSum Q (fun i=>lowerTruncation Q (E i) (hE i) d) := by
  apply ext_placement_differential Q
  · rfl
  · apply Matrix.ext
    rintro ⟨i,x⟩ ⟨j,y⟩
    change Matrix.blockDiagonal' (fun i=>(E i).differential) ⟨i,x.val⟩ ⟨j,y.val⟩=
      Matrix.blockDiagonal' (fun i=>(lowerTruncation Q (E i) (hE i) d).differential) ⟨i,x⟩ ⟨j,y⟩
    by_cases h:i=j
    · subst j; simp only [Matrix.blockDiagonal'_apply_eq]; rfl
    · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h,Matrix.blockDiagonal'_apply_ne _ _ _ h]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
