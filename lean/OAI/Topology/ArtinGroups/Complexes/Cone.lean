import Mathlib
import OAI.Topology.ArtinGroups.Complexes.HomotopyConeMap

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
open Matrix

attribute [local instance] Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I J L:Type u} [Fintype I] [Fintype J] [Fintype L]
  [DecidableEq I] [DecidableEq J] [DecidableEq L]
  {E:BasedComplex Q (K:=K) I} {F:BasedComplex Q (K:=K) J}
  {G:BasedComplex Q (K:=K) L}

omit [Fintype V] [DecidableEq A] in
lemma cone_source_replace_backward_square (e:HomotopyEquivalence Q E G) (f:Map Q G F) :
    f.matrix*projectiveIdentity Q F.placement =
      e.backward.matrix*(e.forward.matrix*f.matrix)+
        (G.differential*(-(e.targetHomotopy*f.matrix))+
          (-(e.targetHomotopy*f.matrix))*F.differential) := by
  have hid : f.matrix*projectiveIdentity Q F.placement=f.matrix :=
    mul_projectiveIdentity Q f.entries
  have hid' : projectiveIdentity Q G.placement*f.matrix=f.matrix :=
    projectiveIdentity_mul Q f.entries
  rw [hid]
  simp only [Matrix.mul_neg,Matrix.neg_mul,← Matrix.mul_assoc]
  rw [e.targetEquation,Matrix.add_mul]
  erw [hid']
  simp only [Matrix.add_mul,Matrix.mul_assoc]
  rw [← f.commute]
  abel

omit [Fintype V] [DecidableEq A] [DecidableEq J] in
lemma cone_source_replace_correction (e:HomotopyEquivalence Q E G) (f:Map Q G F)
    (k:Matrix I L (Q.Zigzag K))
    (hk:k=e.sourceHomotopy*e.forward.matrix-e.forward.matrix*e.targetHomotopy)
    (hkc:E.differential*k+k*G.differential=0) :
    -(E.differential*(-(k*e.targetHomotopy*f.matrix)))+
      (-(e.sourceHomotopy-k*e.backward.matrix))*(e.forward.matrix*f.matrix)+
      (-(k*e.targetHomotopy*f.matrix))*F.differential =
      e.forward.matrix*(-(e.targetHomotopy*f.matrix)) := by
  have kc:E.differential*k=-(k*G.differential) := eq_neg_of_add_eq_zero_left hkc
  have hs:G.differential*e.targetHomotopy+e.targetHomotopy*G.differential =
      e.backward.matrix*e.forward.matrix-projectiveIdentity Q G.placement := by
    rw [e.targetEquation]
    abel
  have ke:ProjectiveEntries Q E.placement G.placement k := by
    rw [hk]
    simpa only [sub_eq_add_neg] using projectiveEntries_add Q
      (projectiveEntries_mul Q e.sourceEntries e.forward.entries)
      (projectiveEntries_neg Q (projectiveEntries_mul Q e.forward.entries e.targetEntries))
  have hid:k*projectiveIdentity Q G.placement=k := mul_projectiveIdentity Q ke
  have hb : -(E.differential*(-(k*e.targetHomotopy*f.matrix)))+
      (-(k*e.targetHomotopy*f.matrix))*F.differential =
      k*f.matrix-(k*e.backward.matrix)*(e.forward.matrix*f.matrix) := by
    calc
      _ = -(k*(G.differential*e.targetHomotopy+e.targetHomotopy*G.differential)*f.matrix) := by
        simp only [Matrix.mul_neg,Matrix.neg_mul,neg_neg,← Matrix.mul_assoc]
        rw [kc]
        simp only [Matrix.neg_mul,Matrix.mul_add,Matrix.add_mul,Matrix.mul_assoc]
        rw [← f.commute]
        abel
      _ = _ := by
        rw [hs,Matrix.mul_sub,Matrix.sub_mul]
        erw [hid]
        simp only [Matrix.mul_assoc]
        abel
  calc
    _ = (-(E.differential*(-(k*e.targetHomotopy*f.matrix)))+
          (-(k*e.targetHomotopy*f.matrix))*F.differential)+
          (-(e.sourceHomotopy-k*e.backward.matrix))*(e.forward.matrix*f.matrix) := by abel
    _ = _ := by
      rw [hb]
      simp only [Matrix.neg_mul,Matrix.sub_mul,Matrix.mul_assoc]
      calc
        _ = (k-e.sourceHomotopy*e.forward.matrix)*f.matrix := by
          simp only [Matrix.sub_mul,Matrix.mul_assoc]
          abel
        _ = _ := by
          rw [hk]
          simp only [Matrix.sub_mul,Matrix.mul_neg,Matrix.mul_assoc]
          abel

noncomputable def HomotopyEquivalence.coneSource (e:HomotopyEquivalence Q E G) (f:Map Q G F) :
    HomotopyEquivalence Q ((e.forward.comp Q f).cone Q) (f.cone Q) := by
  let g:=e.forward.comp Q f
  let k:=e.sourceHomotopy*e.forward.matrix-e.forward.matrix*e.targetHomotopy
  have ke:ProjectiveEntries Q E.placement G.placement k := by
    simpa only [k,sub_eq_add_neg] using projectiveEntries_add Q
      (projectiveEntries_mul Q e.sourceEntries e.forward.entries)
      (projectiveEntries_neg Q (projectiveEntries_mul Q e.forward.entries e.targetEntries))
  have kd:MapDegree Q E.placement G.placement (-1) 0 k := by
    have h₁:=mapDegree_mul Q e.sourceDegree e.forward.degree
    have h₂:=mapDegree_mul Q e.forward.degree e.targetDegree
    simp only [add_zero,zero_add] at h₁ h₂
    simpa only [k,sub_eq_add_neg] using mapDegree_add Q h₁ (mapDegree_neg Q h₂)
  have kc:E.differential*k+k*G.differential=0 := homotopy_coherence_closed Q e
  let h:=e.sourceHomotopy-k*e.backward.matrix
  have he:ProjectiveEntries Q E.placement E.placement h := by
    simpa only [h,sub_eq_add_neg] using projectiveEntries_add Q e.sourceEntries
      (projectiveEntries_neg Q (projectiveEntries_mul Q ke e.backward.entries))
  have hd:MapDegree Q E.placement E.placement (-1) 0 h := by
    simpa only [h,sub_eq_add_neg] using mapDegree_add Q e.sourceDegree
      (mapDegree_neg Q (mapDegree_mul Q kd e.backward.degree))
  have hc:E.differential*h+h*E.differential=
      E.differential*e.sourceHomotopy+e.sourceHomotopy*E.differential := by
    have hz:E.differential*(k*e.backward.matrix)+(k*e.backward.matrix)*E.differential=0 := by
      simp only [Matrix.mul_assoc]
      rw [← e.backward.commute]
      simpa only [Matrix.add_mul,Matrix.mul_assoc,Matrix.zero_mul] using
        congrArg (fun m=>m*e.backward.matrix) kc
    dsimp only [h]
    simp only [Matrix.mul_sub,Matrix.sub_mul]
    calc
      _ = (E.differential*e.sourceHomotopy+e.sourceHomotopy*E.differential)-
          (E.differential*(k*e.backward.matrix)+(k*e.backward.matrix)*E.differential) := by abel
      _ = _ := by rw [hz,sub_zero]
  have pe:ProjectiveEntries Q G.placement F.placement (-(e.targetHomotopy*f.matrix)) :=
    projectiveEntries_neg Q (projectiveEntries_mul Q e.targetEntries f.entries)
  have pd:MapDegree Q G.placement F.placement (-1) 0 (-(e.targetHomotopy*f.matrix)) :=
    mapDegree_neg Q (mapDegree_mul Q e.targetDegree f.degree)
  let a:Map Q (g.cone Q) (f.cone Q):=g.coneMap Q f e.forward (Map.identity Q F) (by
    change _=(e.forward.matrix*f.matrix)*projectiveIdentity Q F.placement
    exact (mul_projectiveIdentity Q (projectiveEntries_mul Q e.forward.entries f.entries)).symm)
  let b:Map Q (f.cone Q) (g.cone Q):=f.homotopyConeMap Q g e.backward (Map.identity Q F)
    (-(e.targetHomotopy*f.matrix)) pe pd (cone_source_replace_backward_square Q e f)
  let s:=Matrix.fromBlocks (-h) (-(k*e.targetHomotopy*f.matrix))
      (0:Matrix J I (Q.Zigzag K)) (0:Matrix J J (Q.Zigzag K))
  let t:=Matrix.fromBlocks (-e.targetHomotopy) (0:Matrix L J (Q.Zigzag K))
      (0:Matrix J L (Q.Zigzag K)) (0:Matrix J J (Q.Zigzag K))
  refine ⟨a,b,s,t,?_,?_,?_,?_,?_,?_⟩
  · exact cone_block_entries Q g g _ _ _ _ (projectiveEntries_neg Q he)
      (projectiveEntries_neg Q (projectiveEntries_mul Q (projectiveEntries_mul Q ke e.targetEntries) f.entries))
      (projectiveEntries_zero Q) (projectiveEntries_zero Q)
  · exact cone_block_entries Q f f _ _ _ _ (projectiveEntries_neg Q e.targetEntries)
      (projectiveEntries_zero Q) (projectiveEntries_zero Q) (projectiveEntries_zero Q)
  · exact cone_block_degree Q g g _ _ _ _ (-1) 0 (mapDegree_neg Q hd)
      (mapDegree_neg Q (mapDegree_mul Q (mapDegree_mul Q kd e.targetDegree) f.degree))
      (mapDegree_zero Q _ _) (mapDegree_zero Q _ _)
  · exact cone_block_degree Q f f _ _ _ _ (-1) 0 (mapDegree_neg Q e.targetDegree)
      (mapDegree_zero Q _ _) (mapDegree_zero Q _ _) (mapDegree_zero Q _ _)
  · change Matrix.fromBlocks e.forward.matrix 0 0 (projectiveIdentity Q F.placement) *
      Matrix.fromBlocks e.backward.matrix (-(e.targetHomotopy*f.matrix)) 0 (projectiveIdentity Q F.placement) =
      projectiveIdentity Q (g.cone Q).placement+
        (Matrix.fromBlocks (-E.differential) g.matrix 0 F.differential*s+
          s*Matrix.fromBlocks (-E.differential) g.matrix 0 F.differential)
    dsimp only [s]
    rw [cone_identity_blocks,Matrix.fromBlocks_multiply,Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply,Matrix.fromBlocks_add,Matrix.fromBlocks_add]
    simp only [Matrix.zero_mul,Matrix.mul_zero,add_zero,zero_add,Matrix.neg_mul,Matrix.mul_neg,neg_neg]
    have hi:projectiveIdentity Q F.placement*projectiveIdentity Q F.placement=
        projectiveIdentity Q F.placement :=
      projectiveIdentity_mul Q (projectiveEntries_identity Q (K:=K) (p:=F.placement))
    erw [hi,hc,← e.sourceEquation]
    simp only [neg_zero,zero_add,add_zero]
    congr 1
    simpa only [h,g,Map.comp,Matrix.neg_mul,Matrix.mul_neg,neg_neg,add_assoc] using
      (cone_source_replace_correction Q e f k rfl kc).symm
  · change Matrix.fromBlocks e.backward.matrix (-(e.targetHomotopy*f.matrix)) 0 (projectiveIdentity Q F.placement) *
      Matrix.fromBlocks e.forward.matrix 0 0 (projectiveIdentity Q F.placement) =
      projectiveIdentity Q (f.cone Q).placement+
        (Matrix.fromBlocks (-G.differential) f.matrix 0 F.differential*t+
          t*Matrix.fromBlocks (-G.differential) f.matrix 0 F.differential)
    dsimp only [t]
    rw [cone_identity_blocks,Matrix.fromBlocks_multiply,Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply,Matrix.fromBlocks_add,Matrix.fromBlocks_add]
    simp only [Matrix.zero_mul,Matrix.mul_zero,add_zero,zero_add,Matrix.neg_mul,Matrix.mul_neg,neg_neg]
    have hi:projectiveIdentity Q F.placement*projectiveIdentity Q F.placement=
        projectiveIdentity Q F.placement :=
      projectiveIdentity_mul Q (projectiveEntries_identity Q (K:=K) (p:=F.placement))
    have hp:(e.targetHomotopy*f.matrix)*projectiveIdentity Q F.placement=
        e.targetHomotopy*f.matrix :=
      mul_projectiveIdentity Q (projectiveEntries_mul Q e.targetEntries f.entries)
    erw [hi,hp,e.targetEquation]
    simp only [neg_zero,zero_add]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
