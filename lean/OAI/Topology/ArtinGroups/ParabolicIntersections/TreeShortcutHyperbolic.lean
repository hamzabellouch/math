import OAI.Topology.ArtinGroups.ParabolicIntersections.TreeTripod
import OAI.Topology.ArtinGroups.ParabolicIntersections.TreeShortcutMetric
import Mathlib.Tactic.Linarith
import Mathlib.Basic.Real.Basic

namespace OAI

/-! Gromov hyperbolicity of a tree with convex shortcuts. -/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V : Type} (T H : SimpleGraph V)

noncomputable def graphProduct (o x y : V) : ℝ :=
  ((H.dist o x : ℝ)+H.dist o y-H.dist x y)/2

lemma graphProduct_branch_bounds (hT : T.IsTree) (hH : H.Connected)
    (hS : PathSaturated T H) {o x y b : V}
    (p : T.Walk o x) (q : T.Walk o y) (r : T.Walk x y)
    (hp : p.IsPath) (hq : q.IsPath) (hr : r.IsPath)
    (hbp : b∈p.support) (hbq : b∈q.support) (hbr : b∈r.support) :
    (H.dist o b : ℝ)-1≤graphProduct H o x y ∧
      graphProduct H o x y≤H.dist o b+1 := by
  have h1 : (H.dist o b : ℝ)+H.dist b x≤H.dist o x+1 := by
    exact_mod_cast shortcut_dist_split T H hT hH hS p hp hbp
  have h2 : (H.dist o b : ℝ)+H.dist b y≤H.dist o y+1 := by
    exact_mod_cast shortcut_dist_split T H hT hH hS q hq hbq
  have h3 : (H.dist b x : ℝ)+H.dist b y≤H.dist x y+1 := by
    have h := shortcut_dist_split T H hT hH hS r hr hbr
    rw [H.dist_comm (u := x) (v := b)] at h
    exact_mod_cast h
  have t1 : (H.dist o x : ℝ)≤H.dist o b+H.dist b x := by
    exact_mod_cast hH.dist_triangle (u := o) (v := b) (w := x)
  have t2 : (H.dist o y : ℝ)≤H.dist o b+H.dist b y := by
    exact_mod_cast hH.dist_triangle (u := o) (v := b) (w := y)
  have t3 : (H.dist x y : ℝ)≤H.dist b x+H.dist b y := by
    have h := hH.dist_triangle (u := x) (v := b) (w := y)
    rw [H.dist_comm (u := x) (v := b)] at h
    exact_mod_cast h
  unfold graphProduct
  constructor <;> linarith

/-- Convex shortcuts preserve hyperbolicity, with a uniform constant. -/
theorem shortcut_graph_hyperbolic (hT : T.IsTree) (hH : H.Connected)
    (hS : PathSaturated T H) (o x y z : V) :
    min (graphProduct H o x y) (graphProduct H o y z)≤graphProduct H o x z+3 := by
  obtain ⟨p,hp⟩ := hT.connected.exists_isPath o x
  obtain ⟨q,hq⟩ := hT.connected.exists_isPath o y
  obtain ⟨r,hr⟩ := hT.connected.exists_isPath o z
  obtain ⟨pxy,hxy⟩ := hT.connected.exists_isPath x y
  obtain ⟨pyz,hyz⟩ := hT.connected.exists_isPath y z
  obtain ⟨pxz,hxz⟩ := hT.connected.exists_isPath x z
  obtain ⟨a,hap,haq,haxy,_⟩ := tree_branchpoint T hT.isAcyclic p q pxy hp hq hxy
  obtain ⟨b,hbq,hbr,hbyz,_⟩ := tree_branchpoint T hT.isAcyclic q r pyz hq hr hyz
  obtain ⟨c,hcp,hcr,hcxz,hcmax⟩ := tree_branchpoint T hT.isAcyclic p r pxz hp hr hxz
  have hga := graphProduct_branch_bounds T H hT hH hS p q pxy hp hq hxy hap haq haxy
  have hgb := graphProduct_branch_bounds T H hT hH hS q r pyz hq hr hyz hbq hbr hbyz
  have hgc := graphProduct_branch_bounds T H hT hH hS p r pxz hp hr hxz hcp hcr hcxz
  rcases prefixes_comparable T q haq hbq with hab|hba
  · have he : q.takeUntil b hbq=r.takeUntil b hbr := congrArg Subtype.val
      (hT.isAcyclic.subsingleton_path o b |>.elim
        ⟨_,hq.takeUntil hbq⟩ ⟨_,hr.takeUntil hbr⟩)
    have har : a∈r.support := r.support_takeUntil_subset_support hbr (he ▸ hab)
    have hac := hcmax a hap har
    have hd := shortcut_dist_split T H hT hH hS (p.takeUntil c hcp) (hp.takeUntil hcp) hac
    have hd' : (H.dist o a : ℝ)≤H.dist o c+1 := by
      have hn : H.dist o a≤H.dist o c+1 := by omega
      exact_mod_cast hn
    calc
      min (graphProduct H o x y) (graphProduct H o y z)≤graphProduct H o x y := min_le_left _ _
      _ ≤ graphProduct H o x z+3 := by linarith [hga.2,hgc.1]
  · have he : q.takeUntil a haq=p.takeUntil a hap := congrArg Subtype.val
      (hT.isAcyclic.subsingleton_path o a |>.elim
        ⟨_,hq.takeUntil haq⟩ ⟨_,hp.takeUntil hap⟩)
    have hbp : b∈p.support := p.support_takeUntil_subset_support hap (he ▸ hba)
    have hbc := hcmax b hbp hbr
    have hd := shortcut_dist_split T H hT hH hS (p.takeUntil c hcp) (hp.takeUntil hcp) hbc
    have hd' : (H.dist o b : ℝ)≤H.dist o c+1 := by
      have hn : H.dist o b≤H.dist o c+1 := by omega
      exact_mod_cast hn
    calc
      min (graphProduct H o x y) (graphProduct H o y z)≤graphProduct H o y z := min_le_right _ _
      _ ≤ graphProduct H o x z+3 := by linarith [hgb.2,hgc.1]

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
