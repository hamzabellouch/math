import Mathlib
import OAI.Topology.ArtinGroups.Complexes.TermwiseSplitInjection

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K:Type*} (Q:ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I J T:Type*} [Fintype I] [Fintype J] [Fintype T]
  [DecidableEq I] [DecidableEq J] [DecidableEq T]

omit [DecidableEq A] [DecidableEq I] in
lemma homDimension_retract_source (M:BasedComplex Q (K:=K) T)
    (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J)
    (ι:Map Q M E) (π:Map Q E M)
    (hret:ι.matrix*π.matrix=projectiveIdentity Q M.placement) (n v:ℤ) :
    homDimension Q M F n v ≤ homDimension Q E F n v := by
  let U:=sandwichHomOperator Q π (Map.identity Q F)
  let W:=sandwichHomOperator Q ι (Map.identity Q F)
  apply LinearMap.finrank_le_finrank_of_injective (f:=U.onCohomology n v)
  apply U.onCohomology_injective
  intro f hf hUf
  have h:=W.map_boundaries n v hUf
  have hcancel:W.component n (U.component n f)=f := by
    change ι.matrix*(π.matrix*f*projectiveIdentity Q (K:=K) F.placement)*
      projectiveIdentity Q (K:=K) F.placement=f
    erw [mul_projectiveIdentity Q (projectiveEntries_mul Q π.entries hf.1.1),
      ← Matrix.mul_assoc,hret,projectiveIdentity_mul Q hf.1.1,
      mul_projectiveIdentity Q hf.1.1]
  rwa [hcancel] at h

omit [Fintype V] [DecidableEq A] [DecidableEq I] [DecidableEq J] [DecidableEq T] in
lemma totalHomDimension_le_of_pointwise (M:BasedComplex Q (K:=K) T)
    (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J) (a b:ℤ)
    (h:∀ v,homDimension Q M E (a-v) v ≤ homDimension Q M F (b-v) v) :
    totalHomDimension Q M E a ≤ totalHomDimension Q M F b := by
  classical
  let D:=homInternalSupport Q M E ∪ homInternalSupport Q M F
  rw [totalHomDimension_eq_sum_of_subset Q M E a D Finset.subset_union_left,
    totalHomDimension_eq_sum_of_subset Q M F b D Finset.subset_union_right]
  exact Finset.sum_le_sum (fun v _=>h v)

omit [DecidableEq A] [DecidableEq I] in
lemma totalHomDimension_retract_source (M:BasedComplex Q (K:=K) T)
    (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J)
    (ι:Map Q M E) (π:Map Q E M)
    (hret:ι.matrix*π.matrix=projectiveIdentity Q M.placement) (t:ℤ) :
    totalHomDimension Q M F t ≤ totalHomDimension Q E F t := by
  classical
  let D:=homInternalSupport Q M F ∪ homInternalSupport Q E F
  rw [totalHomDimension_eq_sum_of_subset Q M F t D Finset.subset_union_left,
    totalHomDimension_eq_sum_of_subset Q E F t D Finset.subset_union_right]
  exact Finset.sum_le_sum (fun v _=>homDimension_retract_source Q M E F ι π hret _ _)

omit [DecidableEq I] [DecidableEq J] in
lemma cappedSummand_total_bound (E:BasedComplex Q (K:=K) I)
    (F:BasedComplex Q (K:=K) J) (hE:E.IsMinimal Q) (hF:F.IsMinimal Q)
    (M:BasedComplex Q (K:=K) T) (U:Set V) (q d:ℤ)
    (hM:∀ i,(M.placement i).level=q) (hU:∀ i,(M.placement i).color∈U)
    (ι:Map Q M (E.pureLayer Q hE q)) (π:Map Q (E.pureLayer Q hE q) M)
    (hret:ι.matrix*π.matrix=projectiveIdentity Q M.placement)
    (hcap:E.CappedOn Q U q)
    (hzero:∀ n v,n+v=d-q → homDimension Q E F n v=0) :
    totalHomDimension Q M (F.pureLayer Q hF d) (d-q) ≤
      totalHomDimension Q (F.pureLayer Q hF (d-1)) M (q-d+1) := by
  have hb:totalHomDimension Q M (F.pureLayer Q hF d) (d-q) ≤
      totalHomDimension Q M (F.pureLayer Q hF (d-1)) (d-q+1) := by
    apply totalHomDimension_le_of_pointwise Q
    intro v
    have f:=cappedSummandInjection Q E F hE hF M U q d (d-q-v) v hM hU ι π
      hret hcap (hzero _ _ (by omega)) (by omega)
    have h:=LinearMap.finrank_le_finrank_of_injective f.property
    change homDimension Q M (F.pureLayer Q hF d) (d-q-v) v ≤
      homDimension Q M (F.pureLayer Q hF (d-1)) (d-q-v+1) v at h
    simpa only [show d-q-v+1=d-q+1-v by omega] using h
  rw [totalHomDimension_dual Q M (F.pureLayer Q hF (d-1)) (d-q+1)] at hb
  simpa only [show 2-(d-q+1)=q-d+1 by omega] using hb

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
