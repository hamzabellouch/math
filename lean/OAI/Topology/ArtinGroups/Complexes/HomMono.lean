import Mathlib
import OAI.Topology.ArtinGroups.Complexes.TargetLow

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I J L:Type u} [Fintype I] [Fintype J] [Fintype L]
  [DecidableEq I] [DecidableEq J] [DecidableEq L]

def HomMonoFrom (T:BasedComplex Q (K:=K) I) {E:BasedComplex Q (K:=K) J}
    {F:BasedComplex Q (K:=K) L} (f:Map Q E F) : Prop :=
  ∀ g, g∈homCycles Q T E 0 0 → g*f.matrix∈homBoundaries Q T F 0 0 →
    g∈homBoundaries Q T E 0 0

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma lowInclusion_homMono (T:BasedComplex Q (K:=K) I)
    (E:BasedComplex Q (K:=K) J) (hE:E.IsMinimal Q) (d:ℤ)
    (hT:∀ i,(T.placement i).level≤d+1) :
    HomMonoFrom Q T (lowInclusion Q E (lowerLevelSet Q E d) (levelDownClosed Q E hE d)) := by
  intro g hg hb
  exact low_boundary_of_inclusion_boundary Q T E hE d hT hg.1.1 hb

lemma positiveHomCohomology_surjective (hn:∀ a,Q.source a≠Q.target a)
    (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J) (α:V) (n v:ℤ) :
    Function.Surjective ((positiveHomOperator Q E F α).onCohomology n v) :=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (positiveTwist_homDimension Q hn E F α n v).symm).mp
      (positiveHomCohomology_injective Q hn E F α n v)

lemma positiveHom_cycle_lift (hn:∀ a,Q.source a≠Q.target a)
    (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J) (α:V) (n v:ℤ)
    {g:Matrix _ _ (Q.Zigzag K)}
    (hg:g∈homCycles Q (E.positiveTwist Q α) (F.positiveTwist Q α) n v) :
    ∃ f, f∈homCycles Q E F n v ∧
      positiveHomTransform Q E F α n f-g∈homBoundaries Q
        (E.positiveTwist Q α) (F.positiveTwist Q α) n v := by
  obtain ⟨x,hx⟩:=positiveHomCohomology_surjective Q hn E F α n v
    (Submodule.Quotient.mk ⟨g,hg⟩)
  obtain ⟨f,rfl⟩:=Submodule.Quotient.mk_surjective _ x
  refine ⟨f,f.property,?_⟩
  have hh:= (Submodule.Quotient.eq
    ((homBoundaries Q (E.positiveTwist Q α) (F.positiveTwist Q α) n v).comap
      (homCycles Q (E.positiveTwist Q α) (F.positiveTwist Q α) n v).subtype)).mp hx
  exact hh

omit [DecidableEq I] [DecidableEq J] [DecidableEq L] in
lemma positiveHom_zero_mul (E:BasedComplex Q (K:=K) I)
    (F:BasedComplex Q (K:=K) J) (G:BasedComplex Q (K:=K) L) (α:V)
    (f:Matrix I J (Q.Zigzag K)) (hf:ProjectiveEntries Q E.placement F.placement f)
    (g:Map Q F G) :
    positiveHomTransform Q E F α 0 f*(g.positiveTwist Q α).matrix=
      positiveHomTransform Q E G α 0 (f*g.matrix) := by
  change Matrix.fromBlocks _ 0 0 f * Matrix.fromBlocks _ 0 0 g.matrix=_
  simp only [positiveHomTransform,cochainSign_zero,one_smul,Matrix.fromBlocks_multiply,
    Matrix.mul_zero,Matrix.zero_mul,zero_add,add_zero,Map.test,testTransform_mul Q α _ hf]

lemma HomMonoFrom.positiveTwist (hn:∀ a,Q.source a≠Q.target a)
    {T:BasedComplex Q (K:=K) I} {E:BasedComplex Q (K:=K) J}
    {F:BasedComplex Q (K:=K) L} {f:Map Q E F}
    (h:HomMonoFrom Q T f) (α:V) :
    HomMonoFrom Q (T.positiveTwist Q α) (f.positiveTwist Q α) := by
  intro g hg hb
  obtain ⟨k,hk,hkg⟩:=positiveHom_cycle_lift Q hn T E α 0 0 hg
  have hh:=homBoundary_mul_cycle Q hkg (map_mem_homCycles Q (f.positiveTwist Q α))
  simp only [zero_add] at hh
  rw [Matrix.sub_mul,positiveHom_zero_mul Q T E F α k hk.1.1 f] at hh
  have hb':positiveHomTransform Q T F α 0 (k*f.matrix)∈homBoundaries Q
      (T.positiveTwist Q α) (F.positiveTwist Q α) 0 0 := by
    have hz:=(homBoundaries Q _ _ 0 0).add_mem hh hb
    simpa only [sub_add_cancel] using hz
  have hkf:ProjectiveEntries Q T.placement F.placement (k*f.matrix):=
    projectiveEntries_mul Q hk.1.1 f.entries
  have hk':=h k hk (positiveHomTransform_reflect_boundary Q hn T F α 0 0 hkf hb')
  have hkb:positiveHomTransform Q T E α 0 k∈homBoundaries Q
      (T.positiveTwist Q α) (E.positiveTwist Q α) 0 0 :=
    (positiveHomOperator Q T E α).map_boundaries 0 0 hk'
  have hz:=(homBoundaries Q (T.positiveTwist Q α) (E.positiveTwist Q α) 0 0).sub_mem hkb hkg
  simpa only [sub_sub_cancel] using hz

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
