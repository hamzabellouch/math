import Mathlib
import OAI.Topology.ArtinGroups.Complexes.PositiveHomTransform
import OAI.Topology.ArtinGroups.Complexes.HomOperator

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I J I' J' : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V] [Fintype I] [Fintype J] [Fintype I'] [Fintype J']

noncomputable def reindexHomOperator (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (e : I' ≃ I) (f : J' ≃ J) :
    HomOperator Q E F (E.reindex Q e) (F.reindex Q f) where
  component _ := {
    toFun g := g.submatrix e f
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  preserves n v g hg := by
    constructor
    · exact ⟨fun i j => hg.1.1 (e i) (f j), fun i j => hg.1.2 (e i) (f j)⟩
    · exact fun i j => hg.2 (e i) (f j)
  commute n v g _ := by
    change E.differential.submatrix e e * g.submatrix e f -
      cochainSign (K := K) n • (g.submatrix e f * F.differential.submatrix f f) =
      (E.differential * g - cochainSign (K := K) n • (g * F.differential)).submatrix e f
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
    rfl

noncomputable def sandwichHomOperator {E : BasedComplex Q (K := K) I}
    {F : BasedComplex Q (K := K) J} {E' : BasedComplex Q (K := K) I'}
    {F' : BasedComplex Q (K := K) J'} (a : Map Q E' E) (b : Map Q F F') :
    HomOperator Q E F E' F' where
  component _ := {
    toFun g := a.matrix * g * b.matrix
    map_add' _ _ := by simp only [Matrix.mul_add, Matrix.add_mul]
    map_smul' _ _ := by simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply] }
  preserves n v g hg := by
    constructor
    · exact projectiveEntries_mul Q (projectiveEntries_mul Q a.entries hg.1) b.entries
    · change MapDegree Q E'.placement F'.placement n v (a.matrix * g * b.matrix)
      simpa only [zero_add, add_zero] using
        mapDegree_mul Q (mapDegree_mul Q a.degree hg.2) b.degree
  commute n _ g _ := homDifferential_sandwich Q a b n g

variable [Fintype V] [DecidableEq A]

noncomputable def positiveHomOperator (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (α : V) :
    HomOperator Q E F (E.positiveTwist Q α) (F.positiveTwist Q α) where
  component n := {
    toFun := positiveHomTransform Q E F α n
    map_add' f g := by
      simp only [positiveHomTransform, testTransform_add, smul_add]
      rw [Matrix.fromBlocks_add]
      simp only [add_zero]
    map_smul' r f := by
      simp only [positiveHomTransform, testTransform_smul, RingHom.id_apply]
      rw [Matrix.fromBlocks_smul, smul_comm r]
      simp only [smul_zero] }
  preserves n v g hg := ⟨positiveHomTransform_entries Q E F α n hg.1,
    positiveHomTransform_degree Q E F α n v hg.2⟩
  commute n _ g hg := positiveHomTransform_differential Q E F α n hg.1

noncomputable def negativeHomOperator (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (α : V) :
    HomOperator Q E F (E.negativeTwist Q α) (F.negativeTwist Q α) where
  component n := {
    toFun := negativeHomTransform Q E F α n
    map_add' f g := by
      simp only [negativeHomTransform, testTransform_add, smul_add]
      rw [Matrix.fromBlocks_add]
      simp only [add_zero]
    map_smul' r f := by
      simp only [negativeHomTransform, testTransform_smul, RingHom.id_apply]
      rw [Matrix.fromBlocks_smul, smul_comm r]
      simp only [smul_zero] }
  preserves n v g hg := ⟨negativeHomTransform_entries Q E F α n hg.1,
    negativeHomTransform_degree Q E F α n v hg.2⟩
  commute n _ g hg := negativeHomTransform_differential Q E F α n hg.1

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
