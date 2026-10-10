import Mathlib
import OAI.Topology.ArtinGroups.Quivers.ProbeVertex

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.ProbeEmbedding
open Zigzag Zigzag.BasedComplex

variable {V A K : Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V]
  [DecidableEq (ProbeVertex V)]
local notation "R" => probeQuiver Q

noncomputable def zigzagLinear : Q.Zigzag K →ₗ[K] (probeQuiver Q).Zigzag K where
  toFun x := (Sum.elim x.vertex (fun _=>0), Sum.elim x.arrow (fun _=>0),
    Sum.elim x.token (fun _=>0))
  map_add' x y := by
    apply Zigzag.ext (Q:=probeQuiver Q) <;> funext z <;> cases z
    all_goals first | rfl | exact (zero_add (0:K)).symm
  map_smul' c x := by
    apply Zigzag.ext (Q:=probeQuiver Q) <;> funext z <;> cases z
    all_goals first | rfl | exact (smul_zero c).symm

@[simp] lemma zigzag_vertex_core (x:Q.Zigzag K) (v:V) :
    (zigzagLinear Q x).vertex (.inl v)=x.vertex v := rfl
@[simp] lemma zigzag_vertex_leaf (x:Q.Zigzag K) (p:V×Bool) :
    (zigzagLinear Q x).vertex (.inr p)=0 := rfl
@[simp] lemma zigzag_arrow_core (x:Q.Zigzag K) (a:A) :
    (zigzagLinear Q x).arrow (.inl a)=x.arrow a := rfl
@[simp] lemma zigzag_arrow_leaf (x:Q.Zigzag K) (p:V×Bool×Bool) :
    (zigzagLinear Q x).arrow (.inr p)=0 := rfl
@[simp] lemma zigzag_token_core (x:Q.Zigzag K) (v:V) :
    (zigzagLinear Q x).token (.inl v)=x.token v := rfl
@[simp] lemma zigzag_token_leaf (x:Q.Zigzag K) (p:V×Bool) :
    (zigzagLinear Q x).token (.inr p)=0 := rfl

lemma zigzagLinear_mul (x y:Q.Zigzag K) :
    zigzagLinear Q (x*y)=zigzagLinear Q x*zigzagLinear Q y := by
  apply Zigzag.ext (Q:=probeQuiver Q)
  · ext z; cases z <;> simp
  · ext z
    rcases z with a|⟨v,b,d⟩
    · rfl
    · cases d
      · change (0:K)= (zigzagLinear Q x).vertex (.inl v)*0+0*(zigzagLinear Q y).vertex (.inr (v,b))
        simp
      · change (0:K)= (zigzagLinear Q x).vertex (.inr (v,b))*0+0*(zigzagLinear Q y).vertex (.inl v)
        simp
  · ext z
    cases z with
    | inl v =>
      rw [zigzag_token_core Q, token_mul (Q:=Q),token_mul (Q:=probeQuiver Q)]
      simp only [Pi.add_apply,Pi.mul_apply,zigzag_vertex_core,zigzag_token_core]
      congr 1
      change Q.backtrack x.arrow y.arrow v =
        (probeQuiver Q).backtrack (Sum.elim x.arrow (fun _=>0)) (Sum.elim y.arrow (fun _=>0)) (.inl v)
      simp [backtrack,probeQuiver,Fintype.sum_sum_type]
    | inr p =>
      rw [zigzag_token_leaf Q,token_mul (Q:=probeQuiver Q)]
      simp only [Pi.add_apply,Pi.mul_apply,zigzag_vertex_leaf,zigzag_token_leaf,MulZeroClass.zero_mul,zero_add]
      change (0:K)=(probeQuiver Q).backtrack (Sum.elim x.arrow (fun _=>0)) (Sum.elim y.arrow (fun _=>0)) (.inr p)
      simp [backtrack,probeQuiver,Fintype.sum_sum_type]

lemma zigzag_vertexId (v:V) : zigzagLinear Q (vertexId Q (K:=K) v)=vertexId R (.inl v) := by
  apply Zigzag.ext (Q:=probeQuiver Q)
  · funext z
    cases z with
    | inl w =>
      rw [zigzag_vertex_core Q, vertexId_eval,vertexId_eval]
      simp
    | inr w => rw [zigzag_vertex_leaf Q,vertexId_eval]; simp
  · funext z; cases z <;> rfl
  · funext z; cases z <;> rfl

lemma zigzag_homogeneous {d:ℤ} {x:Q.Zigzag K} (h:Homogeneous Q d x) :
    Homogeneous R d (zigzagLinear Q x) := by
  refine ⟨?_,?_,?_⟩
  · intro hd; funext z
    cases z with
    | inl z => exact congrFun (h.1 hd) z
    | inr z => rfl
  · intro hd; funext z
    cases z with
    | inl z => exact congrFun (h.2.1 hd) z
    | inr z => rfl
  · intro hd; funext z
    cases z with
    | inl z => exact congrFun (h.2.2 hd) z
    | inr z => rfl

variable {I J L:Type*}
def placement (p:GeneratorPlacement V) : GeneratorPlacement (ProbeVertex V) :=
  ⟨.inl p.color,p.cochain,p.internal⟩

noncomputable def matrix (M:Matrix I J (Q.Zigzag K)) : Matrix I J ((probeQuiver Q).Zigzag K) :=
  M.map (zigzagLinear Q)

@[simp] lemma matrix_apply (M:Matrix I J (Q.Zigzag K)) (i:I) (j:J) :
    matrix Q M i j=zigzagLinear Q (M i j) := rfl
@[simp] lemma matrix_zero : matrix Q (0:Matrix I J (Q.Zigzag K))=0 := by
  apply Matrix.ext; intro i j; exact map_zero (zigzagLinear Q)
@[simp] lemma matrix_add (M N:Matrix I J (Q.Zigzag K)) :
    matrix Q (M+N)=matrix Q M+matrix Q N := by
  apply Matrix.ext; intro i j; exact map_add (zigzagLinear Q) _ _
@[simp] lemma matrix_mul [Fintype J] (M:Matrix I J (Q.Zigzag K)) (N:Matrix J L (Q.Zigzag K)) :
    matrix Q (M*N)=matrix Q M*matrix Q N := by
  apply Matrix.ext
  intro i j
  simp only [matrix_apply,Matrix.mul_apply,map_sum,zigzagLinear_mul]

lemma matrix_entries {p:I → GeneratorPlacement V} {q:J → GeneratorPlacement V}
    {M : Matrix I J (Q.Zigzag K)} (h : ProjectiveEntries Q p q M) :
    ProjectiveEntries (probeQuiver Q) (placement ∘ p) (placement ∘ q) (matrix Q M) := by
  constructor
  · intro i j
    change vertexId (probeQuiver Q) (Sum.inl (p i).color) * zigzagLinear Q (M i j) = _
    rw [← zigzag_vertexId Q,← zigzagLinear_mul Q,h.1]
    rfl
  · intro i j
    change zigzagLinear Q (M i j) * vertexId (probeQuiver Q) (Sum.inl (q j).color) = _
    rw [← zigzag_vertexId Q,← zigzagLinear_mul Q,h.2]
    rfl

lemma matrix_degree {p:I → GeneratorPlacement V} {q:J → GeneratorPlacement V}
    {M : Matrix I J (Q.Zigzag K)} {n v:ℤ} (h : MapDegree Q p q n v M) :
    MapDegree (probeQuiver Q) (placement ∘ p) (placement ∘ q) n v (matrix Q M) := by
  intro i j
  refine ⟨?_,zigzag_homogeneous Q (h i j).2⟩
  intro hn
  change zigzagLinear Q (M i j) = 0
  rw [(h i j).1 hn,map_zero]

@[simp] lemma matrix_identity [DecidableEq I] (p : I → GeneratorPlacement V) :
    matrix Q (projectiveIdentity Q (K := K) p) = projectiveIdentity (probeQuiver Q) (placement ∘ p) := by
  apply Matrix.ext
  intro i j
  by_cases h:i=j
  · subst j
    simp only [matrix,Matrix.map_apply,projectiveIdentity,Matrix.diagonal_apply_eq]
    change zigzagLinear Q (vertexId Q (p i).color) = vertexId (probeQuiver Q) (Sum.inl (p i).color)
    exact zigzag_vertexId Q (K := K) (p i).color
  · simp [matrix,projectiveIdentity,h]

noncomputable def complex [Fintype I] (E : BasedComplex Q (K := K) I) : BasedComplex (probeQuiver Q) (K := K) I where
  placement := placement ∘ E.placement
  differential := matrix Q E.differential
  entries := matrix_entries Q E.entries
  degree := matrix_degree Q E.degree
  square_zero := by rw [← matrix_mul,E.square_zero,matrix_zero]

lemma complex_minimal [Fintype I] {E : BasedComplex Q (K := K) I} (h:E.IsMinimal Q) :
    (complex Q E).IsMinimal (probeQuiver Q) := by
  intro i j
  ext v
  change (zigzagLinear Q (E.differential i j)).vertex v=0
  cases v <;> simp [h i j]

noncomputable def chainMap [Fintype I] [Fintype J]
    {E : BasedComplex Q (K := K) I} {F : BasedComplex Q (K := K) J} (f : Map Q E F) :
    Map (probeQuiver Q) (complex Q E) (complex Q F) where
  matrix := matrix Q f.matrix
  entries := matrix_entries Q f.entries
  degree := matrix_degree Q f.degree
  commute := by
    change matrix Q E.differential * matrix Q f.matrix = matrix Q f.matrix * matrix Q F.differential
    rw [← matrix_mul,← matrix_mul,f.commute]

noncomputable def homotopyEquivalence [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {E : BasedComplex Q (K := K) I} {F : BasedComplex Q (K := K) J} (f : HomotopyEquivalence Q E F) :
    HomotopyEquivalence (probeQuiver Q) (complex Q E) (complex Q F) where
  forward := chainMap Q f.forward
  backward := chainMap Q f.backward
  sourceHomotopy := matrix Q f.sourceHomotopy
  targetHomotopy := matrix Q f.targetHomotopy
  sourceEntries := matrix_entries Q f.sourceEntries
  targetEntries := matrix_entries Q f.targetEntries
  sourceDegree := matrix_degree Q f.sourceDegree
  targetDegree := matrix_degree Q f.targetDegree
  sourceEquation := by
    change matrix Q f.forward.matrix * matrix Q f.backward.matrix = _
    rw [← matrix_mul,f.sourceEquation,matrix_add,matrix_add,matrix_mul,matrix_mul,matrix_identity]
    rfl
  targetEquation := by
    change matrix Q f.backward.matrix * matrix Q f.forward.matrix = _
    rw [← matrix_mul,f.targetEquation,matrix_add,matrix_add,matrix_mul,matrix_mul,matrix_identity]
    rfl

end HarmonicArtin.ReversibleQuiver.ProbeEmbedding

end OAI
