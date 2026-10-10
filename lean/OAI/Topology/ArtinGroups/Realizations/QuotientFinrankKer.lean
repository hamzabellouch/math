import Mathlib
import OAI.Topology.ArtinGroups.Quivers.CornerScalar
import OAI.Topology.ArtinGroups.Complexes.TermwiseSplitInjection

namespace OAI

namespace HarmonicArtin

lemma quotient_finrank_le_of_ker_le {K U W:Type*} [Field K]
    [AddCommGroup U] [Module K U] [Module.Finite K U]
    [AddCommGroup W] [Module K W] [Module.Finite K W]
    (B:Submodule K U) (f:U→ₗ[K]W) (h:LinearMap.ker f≤B) :
    Module.finrank K (U ⧸ B)≤Module.finrank K W := by
  have hq:=B.finrank_quotient_add_finrank
  have hr:=f.finrank_range_add_finrank_ker
  have hk:=Submodule.finrank_mono h
  have hi:=Submodule.finrank_le (LinearMap.range f)
  omega

namespace ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I J I' J':Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [Fintype J] [Fintype I'] [Fintype J']

omit [DecidableEq A] in
lemma homDimension_le_of_cycle_map
    (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J)
    (E':BasedComplex Q (K:=K) I') (F':BasedComplex Q (K:=K) J') (n v:ℤ)
    (T:homCycles Q E F n v→ₗ[K]homCycles Q E' F' n v)
    (hr:∀ f:homCycles Q E F n v,
      (T f).val∈homBoundaries Q E' F' n v→f.val∈homBoundaries Q E F n v) :
    homDimension Q E F n v≤homDimension Q E' F' n v := by
  let B:Submodule K (homCycles Q E F n v):=
    (homBoundaries Q E F n v).comap (homCycles Q E F n v).subtype
  let B':Submodule K (homCycles Q E' F' n v):=
    (homBoundaries Q E' F' n v).comap (homCycles Q E' F' n v).subtype
  apply quotient_finrank_le_of_ker_le B (B'.mkQ.comp T)
  intro f hf
  exact hr f ((Submodule.Quotient.mk_eq_zero B').mp hf)

omit [DecidableEq A] in
theorem middleLayer_homDimension_le
    (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J)
    (hE:E.IsMinimal Q) (hF:F.IsMinimal Q) (l k n v:ℤ) (h:n+v=k-l+1) :
    homDimension Q (E.pureLayer Q hE l) (F.pureLayer Q hF k) n v≤homDimension Q E F n v := by
  let T:homCycles Q (E.pureLayer Q hE l) (F.pureLayer Q hF k) n v→ₗ[K]
      homCycles Q E F n v :=
    (extendLayer Q E F l k).restrict (fun f hf=>
      extendLayer_cycle Q E F hE hF l k n v hf
        (pure_homSpace_linear Q _ _ (fun i=>i.property) (fun j=>j.property) h hf.1))
  apply homDimension_le_of_cycle_map Q _ _ E F n v T
  intro f hf
  exact layer_boundary_of_extended_boundary Q E F hE hF l k n v
    (pure_homSpace_linear Q _ _ (fun i=>i.property) (fun j=>j.property) h f.property.1) hf

omit [Fintype V] [DecidableEq A] in
lemma homSpace_positive_of_vertexLevelBound
    (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J) (r n v:ℤ)
    (hb:∀i j,(E.placement i).color=(F.placement j).color→
      (F.placement j).level-(E.placement i).level≤r) (h:r<n+v)
    {f:Matrix I J (Q.Zigzag K)} (hf:f∈homSpace Q E F n v) : PositiveMatrix Q f := by
  intro i j
  funext α
  by_contra hz
  have hh:=degree_vertex_support Q hf.1 hf.2 i j α hz
  have hb':=hb i j (hh.1.trans hh.2.1.symm)
  dsimp only [GeneratorPlacement.level] at hb'
  omega

omit [Fintype V] [DecidableEq A] in
lemma TokenMatrix.extendLayer
    (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J) (l k:ℤ)
    {f:Matrix {i // (E.placement i).level=l} {j // (F.placement j).level=k} (Q.Zigzag K)}
    (hf:TokenMatrix Q f) : TokenMatrix Q (extendLayer Q E F l k f) := by
  intro i j
  rw [extendLayer_entry]
  split_ifs
  · exact hf _ _
  · exact ⟨rfl,rfl⟩
  · exact ⟨rfl,rfl⟩

omit [Fintype V] [DecidableEq A] in
lemma homDifferential_token_zero
    (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J)
    (hE:E.IsMinimal Q) (hF:F.IsMinimal Q) (n:ℤ)
    {f:Matrix I J (Q.Zigzag K)} (hf:TokenMatrix Q f) : homDifferential Q E F n f=0 := by
  change E.differential*f-cochainSign (K:=K) n • (f*F.differential)=0
  rw [← matrixTwo_eq_self Q hf,positive_mul_matrixTwo Q hE,
    matrixTwo_mul_positive Q _ hF,smul_zero,sub_zero]

omit [Fintype V] [DecidableEq A] in
lemma tokenLayer_boundary_of_extended_boundary
    (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J)
    (hE:E.IsMinimal Q) (hF:F.IsMinimal Q) (l k n v:ℤ) (h:n+v=k-l+2)
    (hb:∀i j,(E.placement i).color=(F.placement j).color→
      (F.placement j).level-(E.placement i).level≤k-l)
    {f:Matrix {i // (E.placement i).level=l} {j // (F.placement j).level=k} (Q.Zigzag K)}
    (hf:extendLayer Q E F l k f∈homBoundaries Q E F n v) :
    f∈homBoundaries Q (E.pureLayer Q hE l) (F.pureLayer Q hF k) n v := by
  obtain ⟨g,hg,he⟩:=hf
  have hp:PositiveMatrix Q g:=homSpace_positive_of_vertexLevelBound Q E F (k-l) (n-1) v
    hb (by omega) hg
  have hd:homDifferential Q E F (n-1) g=linearHomDifferential Q E F (n-1) g := by
    rw [homDifferential_eq_linear_add_token,
      tokenHomDifferential_positive Q E F hE hF _ hp,add_zero]
  rw [hd] at he
  refine ⟨restrictLayer Q E F l k g,restrictLayer_homSpace Q E F hE hF l k (n-1) v hg,?_⟩
  have hh:=congrArg (restrictLayer Q E F l k) he
  change restrictLayer Q E F l k (matrixOne Q E.differential*g-
    cochainSign (K:=K) (n-1) • (g*matrixOne Q F.differential))=_ at hh
  rw [map_sub,map_smul,restrictLayer_matrixOne_mul Q E F hE,
    restrictLayer_mul_matrixOne Q E F hF,restrictLayer_extend] at hh
  exact hh

omit [DecidableEq A] in
theorem tokenLayer_homDimension_le
    (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J)
    (hE:E.IsMinimal Q) (hF:F.IsMinimal Q) (l k n v:ℤ) (h:n+v=k-l+2)
    (hb:∀i j,(E.placement i).color=(F.placement j).color→
      (F.placement j).level-(E.placement i).level≤k-l) :
    homDimension Q (E.pureLayer Q hE l) (F.pureLayer Q hF k) n v≤homDimension Q E F n v := by
  let T:homCycles Q (E.pureLayer Q hE l) (F.pureLayer Q hF k) n v→ₗ[K]
      homCycles Q E F n v :=
    (extendLayer Q E F l k).restrict (fun f hf=>
      ⟨extendLayer_homSpace Q E F hE hF l k n v hf.1,
        homDifferential_token_zero Q E F hE hF n
          (TokenMatrix.extendLayer Q E F l k
            (pure_homSpace_token Q _ _ (fun i=>i.property) (fun j=>j.property) h hf.1))⟩)
  apply homDimension_le_of_cycle_map Q _ _ E F n v T
  intro f hf
  exact tokenLayer_boundary_of_extended_boundary Q E F hE hF l k n v h hb hf

omit [DecidableEq A] in
lemma middleLayer_totalHomDimension_le
    (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J)
    (hE:E.IsMinimal Q) (hF:F.IsMinimal Q) (l k:ℤ) :
    totalHomDimension Q (E.pureLayer Q hE l) (F.pureLayer Q hF k) (k-l+1)≤
      totalHomDimension Q E F (k-l+1) := by
  classical
  let M:=E.pureLayer Q hE l
  let N:=F.pureLayer Q hF k
  let D:=homInternalSupport Q M N ∪ homInternalSupport Q E F
  rw [totalHomDimension_eq_sum_of_subset Q M N (k-l+1) D Finset.subset_union_left,
    totalHomDimension_eq_sum_of_subset Q E F (k-l+1) D Finset.subset_union_right]
  exact Finset.sum_le_sum (fun v _=>middleLayer_homDimension_le Q E F hE hF l k _ v (by omega))

omit [DecidableEq A] in
lemma tokenLayer_totalHomDimension_le
    (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J)
    (hE:E.IsMinimal Q) (hF:F.IsMinimal Q) (l k:ℤ)
    (hb:∀i j,(E.placement i).color=(F.placement j).color→
      (F.placement j).level-(E.placement i).level≤k-l) :
    totalHomDimension Q (E.pureLayer Q hE l) (F.pureLayer Q hF k) (k-l+2)≤
      totalHomDimension Q E F (k-l+2) := by
  classical
  let M:=E.pureLayer Q hE l
  let N:=F.pureLayer Q hF k
  let D:=homInternalSupport Q M N ∪ homInternalSupport Q E F
  rw [totalHomDimension_eq_sum_of_subset Q M N (k-l+2) D Finset.subset_union_left,
    totalHomDimension_eq_sum_of_subset Q E F (k-l+2) D Finset.subset_union_right]
  exact Finset.sum_le_sum (fun v _=>tokenLayer_homDimension_le Q E F hE hF l k _ v (by omega) hb)

end ReversibleQuiver.Zigzag.BasedComplex
end HarmonicArtin

end OAI
