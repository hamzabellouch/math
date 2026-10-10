import Mathlib
import OAI.Topology.ArtinGroups.Complexes.GeneratorArray2
import OAI.Topology.ArtinGroups.Complexes.MinimalModel
import OAI.Topology.ArtinGroups.Complexes.GeneratorVector

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A:Type u} {K I:Type*} [Fintype I] [Field K]
  (Q:ReversibleQuiver V A) [Fintype A] [DecidableEq V]

lemma generatorVector_pureLayer (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q)
    (q:ℤ) (α:V) : generatorVector Q (E.pureLayer Q hE q) α = (E.levelArray Q (α,q):ℝ) := by
  classical
  rw [levelArray_apply]
  unfold generatorVector
  congr 1
  apply Nat.card_congr
  exact
    { toFun := fun i=>⟨i.val.val,i.property,i.val.property⟩
      invFun := fun i=>⟨⟨i.val,i.property.2⟩,i.property.1⟩
      left_inv := fun _=>rfl
      right_inv := fun _=>rfl }

lemma generatorVector_minimalLayer (x:FiniteHomotopyClass Q (K:=K)) (q:ℤ) (α:V) :
    generatorVector Q ((minimalClassModel Q x).complex.pureLayer Q (minimalClassModel_minimal Q x) q) α =
      (classLevelArray Q x (α,q):ℝ) := by
  rw [generatorVector_pureLayer,← classLevelArray_of_minimal Q _ (minimalClassModel_minimal Q x),
    minimalClassModel_class]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
