import Mathlib
import OAI.Topology.ArtinGroups.Quivers.Reduction
import OAI.Topology.ArtinGroups.Harmonic.Level
import OAI.Topology.ArtinGroups.Quivers.CornerScalar

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I J : Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V]
  [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def ScalarSupported (E:BasedComplex Q (K:=K) I) (l c:ℤ) (x:I→K) : Prop :=
  ∀ i,¬ ((E.placement i).level=l ∧ (E.placement i).cochain=c)→x i=0

def ScalarExactAt (E:BasedComplex Q (K:=K) I) (α:V) (l c:ℤ) : Prop :=
  ∀ x:I→K,ScalarSupported Q E l c x→
    Matrix.vecMul x (E.differential.map (vertexHom Q α))=0→
    ∃ y:I→K,ScalarSupported Q E (l-1) (c-1) y ∧
      Matrix.vecMul y (E.differential.map (vertexHom Q α))=x

omit [DecidableEq I] in
lemma scalarSupported_sub (E:BasedComplex Q (K:=K) I) {l c:ℤ} {x y:I→K}
    (hx:ScalarSupported Q E l c x) (hy:ScalarSupported Q E l c y) :
    ScalarSupported Q E l c (x-y) := by
  intro i hi
  change x i-y i=0
  rw [hx i hi,hy i hi,sub_self]

omit [DecidableEq I] [DecidableEq J] in
lemma scalarSupported_map (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J)
    (α:V) {l c n v:ℤ} (M:Matrix I J (Q.Zigzag K))
    (he:ProjectiveEntries Q E.placement F.placement M)
    (hd:MapDegree Q E.placement F.placement n v M)
    {x:I→K} (hx:ScalarSupported Q E l c x) :
    ScalarSupported Q F (l+n+v) (c+n) (Matrix.vecMul x (M.map (vertexHom Q α))) := by
  intro j hj
  apply Finset.sum_eq_zero
  intro i hi
  change x i * (M i j).vertex α=0
  by_cases hxi:x i=0
  · rw [hxi,MulZeroClass.zero_mul]
  by_cases hm:(M i j).vertex α=0
  · rw [hm,MulZeroClass.mul_zero]
  have hp:(E.placement i).level=l ∧ (E.placement i).cochain=c :=
    Classical.not_not.mp (fun h=>hxi (hx i h))
  obtain ⟨_,_,hc,hu⟩:=degree_vertex_support Q he hd i j α hm
  exact (hj (by dsimp only [GeneratorPlacement.level] at *; constructor <;> omega)).elim

omit [DecidableEq I] in
lemma scalarDifferential_square (E:BasedComplex Q (K:=K) I) (α:V) :
    E.differential.map (vertexHom Q α) * E.differential.map (vertexHom Q α)=0 := by
  rw [← Matrix.map_mul,E.square_zero]
  apply Matrix.ext
  intro i j
  change (vertexHom Q α) (0:Q.Zigzag K)=0
  exact map_zero _

theorem scalarExact_transport (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J)
    (e:HomotopyEquivalence Q E F) (α:V) (hcolor:∀ i,(E.placement i).color=α)
    {l c:ℤ} (hF:ScalarExactAt Q F α l c) : ScalarExactAt Q E α l c := by
  intro x hx hdx
  let f:=e.forward.matrix.map (vertexHom Q α)
  let b:=e.backward.matrix.map (vertexHom Q α)
  let h:=e.sourceHomotopy.map (vertexHom Q α)
  let dE:=E.differential.map (vertexHom Q α)
  let dF:=F.differential.map (vertexHom Q α)
  have hf: dE*f=f*dF := by
    simpa only [Matrix.map_mul] using congrArg
      (fun M:Matrix I J (Q.Zigzag K)=>M.map (vertexHom Q α)) e.forward.commute
  have hb:dF*b=b*dE := by
    simpa only [Matrix.map_mul] using congrArg
      (fun M:Matrix J I (Q.Zigzag K)=>M.map (vertexHom Q α)) e.backward.commute
  have hs:ScalarSupported Q F l c (Matrix.vecMul x f) := by
    simpa only [add_zero] using scalarSupported_map Q E F α e.forward.matrix
      e.forward.entries e.forward.degree hx
  have hd:Matrix.vecMul (Matrix.vecMul x f) dF=0 := by
    rw [Matrix.vecMul_vecMul,← hf,← Matrix.vecMul_vecMul]
    change Matrix.vecMul (Matrix.vecMul x dE) f=0
    rw [hdx,Matrix.zero_vecMul]
  obtain ⟨y,hy,hdy⟩:=hF (Matrix.vecMul x f) hs hd
  refine ⟨Matrix.vecMul y b-Matrix.vecMul x h,?_,?_⟩
  · apply scalarSupported_sub Q E
    · simpa only [add_zero] using scalarSupported_map Q F E α e.backward.matrix
        e.backward.entries e.backward.degree hy
    · convert scalarSupported_map Q E E α e.sourceHomotopy e.sourceEntries e.sourceDegree hx using 1 <;> congr 1; omega
  · have hid:(projectiveIdentity Q (K:=K) E.placement).map (vertexHom Q α)=1 := by
      apply Matrix.ext
      intro i j
      by_cases he:i=j
      · subst j
        simp only [Matrix.one_apply,Matrix.map_apply,projectiveIdentity,Matrix.diagonal_apply]
        change (vertexId Q (K:=K) (E.placement i).color).vertex α=1
        simp [hcolor i,vertexId_eval]
      · simp [projectiveIdentity,Matrix.map_apply,he,vertexHom]
    have he:f*b=1+dE*h+h*dE := by
      simpa only [Matrix.map_mul,Matrix.map_add _ (map_add _),hid,← add_assoc] using congrArg
        (fun M:Matrix I I (Q.Zigzag K)=>M.map (vertexHom Q α)) e.sourceEquation
    have hh:Matrix.vecMul (Matrix.vecMul x f) b=x+Matrix.vecMul (Matrix.vecMul x h) dE := by
      rw [Matrix.vecMul_vecMul,he,Matrix.vecMul_add,Matrix.vecMul_add,
        Matrix.vecMul_one,← Matrix.vecMul_vecMul]
      change x+Matrix.vecMul (Matrix.vecMul x dE) h+_= _
      rw [hdx,Matrix.zero_vecMul,add_zero,← Matrix.vecMul_vecMul]
    change Matrix.vecMul (Matrix.vecMul y b-Matrix.vecMul x h) dE=x
    rw [Matrix.sub_vecMul,Matrix.vecMul_vecMul,← hb,← Matrix.vecMul_vecMul,hdy,hh]
    exact add_sub_cancel_right _ _

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
