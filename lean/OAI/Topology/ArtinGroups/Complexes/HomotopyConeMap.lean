import Mathlib
import OAI.Topology.ArtinGroups.Complexes.InverseMatrix

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
open Matrix

attribute [local instance] Classical.propDecidable
attribute [local instance 2000] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I J L N:Type u} [Fintype I] [Fintype J] [Fintype L] [Fintype N]
  [DecidableEq I] [DecidableEq J] [DecidableEq L] [DecidableEq N]
  {E:BasedComplex Q (K:=K) I} {F:BasedComplex Q (K:=K) J}
  {G:BasedComplex Q (K:=K) L} {D:BasedComplex Q (K:=K) N}

omit [Fintype V] [DecidableEq A] [DecidableEq I] [DecidableEq J]
  [DecidableEq L] [DecidableEq N] in
lemma cone_block_entries (f:Map Q E F) (g:Map Q G D)
    (a:Matrix I L (Q.Zigzag K)) (b:Matrix I N (Q.Zigzag K))
    (c:Matrix J L (Q.Zigzag K)) (d:Matrix J N (Q.Zigzag K))
    (ha:ProjectiveEntries Q E.placement G.placement a)
    (hb:ProjectiveEntries Q E.placement D.placement b)
    (hc:ProjectiveEntries Q F.placement G.placement c)
    (hd:ProjectiveEntries Q F.placement D.placement d) :
    ProjectiveEntries Q (f.cone Q).placement (g.cone Q).placement
      (Matrix.fromBlocks a b c d) := by
  constructor <;> intro i j <;> rcases i with i|i <;> rcases j with j|j
  · exact ha.1 i j
  · exact hb.1 i j
  · exact hc.1 i j
  · exact hd.1 i j
  · exact ha.2 i j
  · exact hb.2 i j
  · exact hc.2 i j
  · exact hd.2 i j

omit [Fintype V] [DecidableEq A] [DecidableEq I] [DecidableEq J]
  [DecidableEq L] [DecidableEq N] in
lemma cone_block_degree (f:Map Q E F) (g:Map Q G D)
    (a:Matrix I L (Q.Zigzag K)) (b:Matrix I N (Q.Zigzag K))
    (c:Matrix J L (Q.Zigzag K)) (d:Matrix J N (Q.Zigzag K)) (n v:ℤ)
    (ha:MapDegree Q E.placement G.placement n v a)
    (hb:MapDegree Q E.placement D.placement (n-1) v b)
    (hc:MapDegree Q F.placement G.placement (n+1) v c)
    (hd:MapDegree Q F.placement D.placement n v d) :
    MapDegree Q (f.cone Q).placement (g.cone Q).placement n v
      (Matrix.fromBlocks a b c d) := by
  intro i j
  rcases i with i|i <;> rcases j with j|j
  · refine ⟨?_,(ha i j).2⟩
    intro h
    apply (ha i j).1
    change (G.placement j).cochain-1≠(E.placement i).cochain-1+n at h
    omega
  · refine ⟨?_,(hb i j).2⟩
    intro h
    apply (hb i j).1
    change (D.placement j).cochain≠(E.placement i).cochain-1+n at h
    omega
  · refine ⟨?_,(hc i j).2⟩
    intro h
    apply (hc i j).1
    change (G.placement j).cochain-1≠(F.placement i).cochain+n at h
    omega
  · exact hd i j

noncomputable def Map.homotopyConeMap (f:Map Q E F) (g:Map Q G D)
    (a:Map Q E G) (b:Map Q F D) (h:Matrix I N (Q.Zigzag K))
    (he:ProjectiveEntries Q E.placement D.placement h)
    (hd:MapDegree Q E.placement D.placement (-1) 0 h)
    (hc:f.matrix*b.matrix=a.matrix*g.matrix+(E.differential*h+h*D.differential)) :
    Map Q (f.cone Q) (g.cone Q) where
  matrix:=Matrix.fromBlocks a.matrix h 0 b.matrix
  entries:=cone_block_entries Q f g _ _ _ _ a.entries he (projectiveEntries_zero Q) b.entries
  degree:=cone_block_degree Q f g _ _ _ _ 0 0 a.degree hd (mapDegree_zero Q _ _) b.degree
  commute:=by
    change Matrix.fromBlocks (-E.differential) f.matrix 0 F.differential *
      Matrix.fromBlocks a.matrix h 0 b.matrix =
      Matrix.fromBlocks a.matrix h 0 b.matrix *
      Matrix.fromBlocks (-G.differential) g.matrix 0 D.differential
    rw [Matrix.fromBlocks_multiply,Matrix.fromBlocks_multiply]
    simp only [Matrix.neg_mul,Matrix.mul_neg,Matrix.mul_zero,Matrix.zero_mul,
      add_zero,zero_add,neg_zero,a.commute,b.commute]
    congr 1
    rw [hc]
    abel

omit [Fintype V] [DecidableEq A] in
lemma homotopy_coherence_closed (e:HomotopyEquivalence Q F G) :
    F.differential*(e.sourceHomotopy*e.forward.matrix-e.forward.matrix*e.targetHomotopy)+
      (e.sourceHomotopy*e.forward.matrix-e.forward.matrix*e.targetHomotopy)*G.differential=0 := by
  have hs:=congrArg (fun m=>m*e.forward.matrix) e.sourceEquation
  have ht:=congrArg (fun m=>e.forward.matrix*m) e.targetEquation
  have hid₁ : projectiveIdentity Q F.placement*e.forward.matrix=e.forward.matrix :=
    projectiveIdentity_mul Q e.forward.entries
  have hid₂ : e.forward.matrix*projectiveIdentity Q G.placement=e.forward.matrix :=
    mul_projectiveIdentity Q e.forward.entries
  erw [Matrix.add_mul,hid₁] at hs
  erw [Matrix.mul_add,hid₂] at ht
  have hh:(F.differential*e.sourceHomotopy+e.sourceHomotopy*F.differential)*e.forward.matrix=
      e.forward.matrix*(G.differential*e.targetHomotopy+e.targetHomotopy*G.differential) := by
    apply add_left_cancel (a:=e.forward.matrix)
    rw [← hs,← ht,Matrix.mul_assoc]
  have hc₁ : (e.sourceHomotopy*e.forward.matrix)*G.differential=
      (e.sourceHomotopy*F.differential)*e.forward.matrix := by
    rw [Matrix.mul_assoc,← e.forward.commute,← Matrix.mul_assoc]
  have hc₂ : F.differential*(e.forward.matrix*e.targetHomotopy)=
      (e.forward.matrix*G.differential)*e.targetHomotopy := by
    rw [← Matrix.mul_assoc,e.forward.commute]
  have hr : F.differential*(e.sourceHomotopy*e.forward.matrix-e.forward.matrix*e.targetHomotopy)+
      (e.sourceHomotopy*e.forward.matrix-e.forward.matrix*e.targetHomotopy)*G.differential =
      (F.differential*e.sourceHomotopy+e.sourceHomotopy*F.differential)*e.forward.matrix-
      e.forward.matrix*(G.differential*e.targetHomotopy+e.targetHomotopy*G.differential) := by
    simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.add_mul,Matrix.mul_add]
    rw [hc₁,hc₂]
    simp only [← Matrix.mul_assoc]
    abel
  rw [hr,hh,sub_self]

omit [Fintype V] [DecidableEq A] in
lemma cone_target_replace_backward_square (f:Map Q E F) (e:HomotopyEquivalence Q F G) :
    (f.matrix*e.forward.matrix)*e.backward.matrix =
      projectiveIdentity Q E.placement*f.matrix+
        (E.differential*(f.matrix*e.sourceHomotopy)+(f.matrix*e.sourceHomotopy)*F.differential) := by
  have hid : projectiveIdentity Q E.placement*f.matrix=f.matrix :=
    projectiveIdentity_mul Q f.entries
  have hid' : f.matrix*projectiveIdentity Q F.placement=f.matrix :=
    mul_projectiveIdentity Q f.entries
  erw [hid,Matrix.mul_assoc,e.sourceEquation,Matrix.mul_add,hid',Matrix.mul_add]
  simp only [← Matrix.mul_assoc]
  rw [f.commute]

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma cone_target_replace_correction (f:Map Q E F) (e:HomotopyEquivalence Q F G)
    (k:Matrix J L (Q.Zigzag K))
    (hk:k=e.sourceHomotopy*e.forward.matrix-e.forward.matrix*e.targetHomotopy)
    (hkc:F.differential*k+k*G.differential=0) :
    -(E.differential*(f.matrix*e.sourceHomotopy*k))+
      (f.matrix*e.forward.matrix)*(e.targetHomotopy+e.backward.matrix*k)+
      (f.matrix*e.sourceHomotopy*k)*G.differential =
      (f.matrix*e.sourceHomotopy)*e.forward.matrix := by
  have hb : -(E.differential*(f.matrix*e.sourceHomotopy*k))+
      (f.matrix*e.sourceHomotopy*k)*G.differential =
      f.matrix*k-(f.matrix*e.forward.matrix)*(e.backward.matrix*k) := by
    have hkc' : k*G.differential=-(F.differential*k) :=
      eq_neg_of_add_eq_zero_right hkc
    have hs : F.differential*e.sourceHomotopy+e.sourceHomotopy*F.differential =
        e.forward.matrix*e.backward.matrix-projectiveIdentity Q F.placement := by
      rw [e.sourceEquation]
      abel
    calc
      _ = -(f.matrix*((F.differential*e.sourceHomotopy+e.sourceHomotopy*F.differential)*k)) := by
        simp only [Matrix.mul_add,Matrix.add_mul,Matrix.mul_assoc]
        rw [hkc']
        simp only [Matrix.mul_neg,← Matrix.mul_assoc,neg_add_rev]
        rw [f.commute]
        abel
      _ = f.matrix*k-(f.matrix*e.forward.matrix)*(e.backward.matrix*k) := by
        rw [hs,Matrix.sub_mul,Matrix.mul_sub]
        have hid : projectiveIdentity Q F.placement*k=k := by
          rw [hk]
          apply projectiveIdentity_mul Q
          simpa only [sub_eq_add_neg] using projectiveEntries_add Q
            (projectiveEntries_mul Q e.sourceEntries e.forward.entries)
            (projectiveEntries_neg Q (projectiveEntries_mul Q e.forward.entries e.targetEntries))
        erw [hid]
        simp only [Matrix.mul_assoc]
        abel
  have hsum : (f.matrix*e.forward.matrix)*(e.targetHomotopy+e.backward.matrix*k) =
      (f.matrix*e.forward.matrix)*e.targetHomotopy+
        (f.matrix*e.forward.matrix)*(e.backward.matrix*k) := Matrix.mul_add _ _ _
  rw [hsum]
  calc
    _ = (-(E.differential*(f.matrix*e.sourceHomotopy*k))+
          (f.matrix*e.sourceHomotopy*k)*G.differential)+
        ((f.matrix*e.forward.matrix)*e.targetHomotopy+
          (f.matrix*e.forward.matrix)*(e.backward.matrix*k)) := by abel
    _ = (f.matrix*e.sourceHomotopy)*e.forward.matrix := by
      rw [hb,hk,Matrix.mul_sub]
      simp only [Matrix.mul_assoc]
      abel

noncomputable def HomotopyEquivalence.coneTarget (e:HomotopyEquivalence Q F G) (f:Map Q E F) :
    HomotopyEquivalence Q (f.cone Q) ((f.comp Q e.forward).cone Q) := by
  let g:=f.comp Q e.forward
  let k:=e.sourceHomotopy*e.forward.matrix-e.forward.matrix*e.targetHomotopy
  have ke:ProjectiveEntries Q F.placement G.placement k := by
    simpa only [k,sub_eq_add_neg] using projectiveEntries_add Q
      (projectiveEntries_mul Q e.sourceEntries e.forward.entries)
      (projectiveEntries_neg Q (projectiveEntries_mul Q e.forward.entries e.targetEntries))
  have kd:MapDegree Q F.placement G.placement (-1) 0 k := by
    have h₁:=mapDegree_mul Q e.sourceDegree e.forward.degree
    have h₂:=mapDegree_mul Q e.forward.degree e.targetDegree
    simp only [add_zero,zero_add] at h₁ h₂
    simpa only [k,sub_eq_add_neg] using mapDegree_add Q h₁ (mapDegree_neg Q h₂)
  have kc:F.differential*k+k*G.differential=0 := homotopy_coherence_closed Q e
  let j:=e.targetHomotopy+e.backward.matrix*k
  have je:ProjectiveEntries Q G.placement G.placement j :=
    projectiveEntries_add Q e.targetEntries (projectiveEntries_mul Q e.backward.entries ke)
  have jd:MapDegree Q G.placement G.placement (-1) 0 j :=
    mapDegree_add Q e.targetDegree (mapDegree_mul Q e.backward.degree kd)
  have jc:G.differential*j+j*G.differential=
      G.differential*e.targetHomotopy+e.targetHomotopy*G.differential := by
    have hz:G.differential*(e.backward.matrix*k)+(e.backward.matrix*k)*G.differential=0 := by
      rw [← Matrix.mul_assoc,e.backward.commute]
      simpa only [Matrix.mul_add,Matrix.mul_assoc,Matrix.mul_zero] using
        congrArg (fun m=>e.backward.matrix*m) kc
    dsimp only [j]
    simp only [Matrix.mul_add,Matrix.add_mul]
    calc
      _ = (G.differential*e.targetHomotopy+e.targetHomotopy*G.differential)+
          (G.differential*(e.backward.matrix*k)+(e.backward.matrix*k)*G.differential) := by abel
      _ = _ := by rw [hz,add_zero]
  have pe:ProjectiveEntries Q E.placement F.placement (f.matrix*e.sourceHomotopy) :=
    projectiveEntries_mul Q f.entries e.sourceEntries
  have pd:MapDegree Q E.placement F.placement (-1) 0 (f.matrix*e.sourceHomotopy) :=
    mapDegree_mul Q f.degree e.sourceDegree
  let a:Map Q (f.cone Q) (g.cone Q):=f.coneMap Q g (Map.identity Q E) e.forward (by
    change projectiveIdentity Q E.placement*(f.matrix*e.forward.matrix)=_
    exact projectiveIdentity_mul Q (projectiveEntries_mul Q f.entries e.forward.entries))
  let b:Map Q (g.cone Q) (f.cone Q):=g.homotopyConeMap Q f (Map.identity Q E) e.backward
    (f.matrix*e.sourceHomotopy) pe pd (cone_target_replace_backward_square Q f e)
  let h:=Matrix.fromBlocks (0:Matrix I I (Q.Zigzag K)) (0:Matrix I J (Q.Zigzag K))
      (0:Matrix J I (Q.Zigzag K)) e.sourceHomotopy
  let t:=Matrix.fromBlocks (0:Matrix I I (Q.Zigzag K)) (f.matrix*e.sourceHomotopy*k)
      (0:Matrix L I (Q.Zigzag K)) j
  refine ⟨a,b,h,t,?_,?_,?_,?_,?_,?_⟩
  · exact cone_block_entries Q f f _ _ _ _ (projectiveEntries_zero Q)
      (projectiveEntries_zero Q) (projectiveEntries_zero Q) e.sourceEntries
  · exact cone_block_entries Q g g _ _ _ _ (projectiveEntries_zero Q)
      (projectiveEntries_mul Q pe ke) (projectiveEntries_zero Q) je
  · exact cone_block_degree Q f f _ _ _ _ (-1) 0 (mapDegree_zero Q _ _)
      (mapDegree_zero Q _ _) (mapDegree_zero Q _ _) e.sourceDegree
  · exact cone_block_degree Q g g _ _ _ _ (-1) 0 (mapDegree_zero Q _ _)
      (mapDegree_mul Q pd kd) (mapDegree_zero Q _ _) jd
  · change Matrix.fromBlocks (projectiveIdentity Q E.placement) 0 0 e.forward.matrix *
      Matrix.fromBlocks (projectiveIdentity Q E.placement) (f.matrix*e.sourceHomotopy) 0 e.backward.matrix =
      projectiveIdentity Q (f.cone Q).placement+
        (Matrix.fromBlocks (-E.differential) f.matrix 0 F.differential*h+
          h*Matrix.fromBlocks (-E.differential) f.matrix 0 F.differential)
    dsimp only [h]
    rw [cone_identity_blocks,Matrix.fromBlocks_multiply,Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply,Matrix.fromBlocks_add,Matrix.fromBlocks_add]
    simp only [Matrix.zero_mul,Matrix.mul_zero,add_zero,zero_add]
    have hi:projectiveIdentity Q E.placement*projectiveIdentity Q E.placement=
        projectiveIdentity Q E.placement :=projectiveIdentity_mul Q (projectiveEntries_identity Q (K:=K) (p:=E.placement))
    have hp:projectiveIdentity Q E.placement*(f.matrix*e.sourceHomotopy)=
        f.matrix*e.sourceHomotopy := projectiveIdentity_mul Q pe
    erw [hi,hp,e.sourceEquation]
  · change Matrix.fromBlocks (projectiveIdentity Q E.placement) (f.matrix*e.sourceHomotopy) 0 e.backward.matrix *
      Matrix.fromBlocks (projectiveIdentity Q E.placement) 0 0 e.forward.matrix =
      projectiveIdentity Q (g.cone Q).placement+
        (Matrix.fromBlocks (-E.differential) g.matrix 0 G.differential*t+
          t*Matrix.fromBlocks (-E.differential) g.matrix 0 G.differential)
    dsimp only [t]
    rw [cone_identity_blocks,Matrix.fromBlocks_multiply,Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply,Matrix.fromBlocks_add,Matrix.fromBlocks_add]
    simp only [Matrix.zero_mul,Matrix.mul_zero,add_zero,zero_add,Matrix.neg_mul]
    have hi:projectiveIdentity Q E.placement*projectiveIdentity Q E.placement=
        projectiveIdentity Q E.placement :=projectiveIdentity_mul Q (projectiveEntries_identity Q (K:=K) (p:=E.placement))
    erw [hi,jc,← e.targetEquation]
    congr 1
    exact (cone_target_replace_correction Q f e k rfl kc).symm

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
