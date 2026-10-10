import OAI.Topology.ArtinGroups.ParabolicIntersections.TreePaths
import OAI.Topology.ArtinGroups.ParabolicIntersections.TreeActionDefinitions
import OAI.Topology.ArtinGroups.ParabolicIntersections.TreePathMetric

namespace OAI

/-! Iterating a tree segment without backtracking produces an actual translation axis. -/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
attribute [local instance] Classical.decEq Classical.propDecidable
variable {G V : Type} [Group G] [MulAction G V]
variable (T : SimpleGraph V) (hA : PreservesAdj (G := G) T)

private abbrev shiftHom (g : G) : T →g T := ⟨(g • ·),hA g⟩

def periodicPath (g : G) {x : V} (p : T.Walk x (g • x)) :
    (n : ℕ) → T.Walk x (g^n • x)
  | 0 => (.nil : T.Walk x x).copy rfl (by simp)
  | n+1 => ((periodicPath g p n).append (p.map (shiftHom T hA (g^n)))).copy rfl
      (by change g^n • (g • x)=g^(n+1) • x; rw [←mul_smul,←pow_succ])

lemma periodicPath_length (g : G) {x : V} (p : T.Walk x (g • x)) (n : ℕ) :
    (periodicPath T hA g p n).length=n*p.length := by
  induction n with
  | zero => simp [periodicPath]
  | succ n ih =>
    simp only [periodicPath,SimpleGraph.Walk.length_copy]
    calc
      _ = (periodicPath T hA g p n).length+(p.map (shiftHom T hA (g^n))).length :=
        SimpleGraph.Walk.length_append _ _
      _ = (n+1)*p.length := by rw [ih,SimpleGraph.Walk.length_map,Nat.add_mul,one_mul]

private lemma first_append_nonempty {x y z : V} (p : T.Walk x y) (q : T.Walk y z)
    (hp : ¬p.Nil) : (p.append q).snd=p.snd := by
  cases p with
  | nil => exact (hp .nil).elim
  | cons h p => simp only [SimpleGraph.Walk.cons_append,SimpleGraph.Walk.snd_cons]

lemma periodicPath_reverse_snd (g : G) {x : V} (p : T.Walk x (g • x))
    (hp : ¬p.Nil) (n : ℕ) :
    (periodicPath T hA g p (n+1)).reverse.snd=g^n • p.reverse.snd := by
  unfold periodicPath
  rw [SimpleGraph.Walk.reverse_copy]
  simp only [SimpleGraph.Walk.getVert_copy]
  rw [SimpleGraph.Walk.reverse_append (periodicPath T hA g p n) (p.map (shiftHom T hA (g^n)))]
  change ((p.map (shiftHom T hA (g^n))).reverse.append
    (periodicPath T hA g p n).reverse).snd= _
  rw [first_append_nonempty T _ _ (by
    intro hn
    have hl := hn.length_eq_zero
    simp only [SimpleGraph.Walk.length_reverse,SimpleGraph.Walk.length_map] at hl
    exact hp (SimpleGraph.Walk.length_eq_zero_iff.mp hl))]
  rw [SimpleGraph.Walk.reverse_map]
  exact SimpleGraph.Walk.getVert_map _ _ 1

private lemma nil_copy_append {x y z : V} (h : x=y) (q : T.Walk y z) :
    ((.nil : T.Walk x x).copy rfl h).append q=q.copy h.symm rfl := by
  subst y
  rfl

theorem periodicPath_isPath (hT : T.IsAcyclic) (g : G) {x : V}
    (p : T.Walk x (g • x)) (hp : p.IsPath) (hpn : ¬p.Nil)
    (hturn : p.reverse.snd≠g • p.snd) (n : ℕ) :
    (periodicPath T hA g p n).IsPath := by
  induction n with
  | zero => simp [periodicPath]
  | succ n ih =>
    apply (SimpleGraph.Walk.isPath_copy _ _ _).mpr
    have hmap : (p.map (shiftHom T hA (g^n))).IsPath := hp.map (MulAction.toPerm (g^n)).injective
    by_cases hn : n=0
    · subst n
      simp only [periodicPath,nil_copy_append]
      exact (SimpleGraph.Walk.isPath_copy _ _ _).mpr hmap
    · obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
      have hne : (periodicPath T hA g p (k+1)).reverse.snd≠
          (p.map (shiftHom T hA (g^(k+1)))).snd := by
        rw [periodicPath_reverse_snd T hA g p hpn k]
        change g^k • p.reverse.snd ≠ (p.map (shiftHom T hA (g^(k+1)))).getVert 1
        rw [SimpleGraph.Walk.getVert_map]
        change g^k • p.reverse.snd ≠ g^(k+1) • p.snd
        rw [pow_succ,mul_smul]
        exact fun he => hturn ((MulAction.toPerm (g^k)).injective he)
      have h := reverse_append_isPath T hT
        (periodicPath T hA g p (k+1)).reverse (p.map (shiftHom T hA (g^(k+1))))
        ih.reverse hmap hne
      simpa only [SimpleGraph.Walk.reverse_reverse] using h

include hA in
theorem periodic_orbit_distance (hT : T.IsAcyclic) (g : G) {x : V}
    (p : T.Walk x (g • x)) (hp : p.IsPath) (hpn : ¬p.Nil)
    (hturn : p.reverse.snd≠g • p.snd) (n : ℕ) :
    T.dist x (g^n • x)=n*p.length := by
  rw [←path_length_eq_dist T hT _ (periodicPath_isPath T hA hT g p hp hpn hturn n),
    periodicPath_length]

lemma periodicPath_support_step (g : G) {x : V} (p : T.Walk x (g • x)) (n : ℕ) :
    (periodicPath T hA g p n).support ⊆ (periodicPath T hA g p (n+1)).support := by
  simp only [periodicPath,SimpleGraph.Walk.support_copy]
  exact SimpleGraph.Walk.support_subset_support_append_left _ _

lemma periodicPath_translate_mem (g : G) {x w : V} (p : T.Walk x (g • x))
    (hw : w∈p.support) (n : ℕ) :
    g^n • w∈(periodicPath T hA g p (n+1)).support := by
  simp only [periodicPath,SimpleGraph.Walk.support_copy]
  apply SimpleGraph.Walk.support_subset_support_append_right
  rw [SimpleGraph.Walk.support_map]
  exact List.mem_map.mpr ⟨w,hw,rfl⟩

lemma periodicPath_translate_mem_of_lt (g : G) {x w : V} (p : T.Walk x (g • x))
    (hw : w∈p.support) (k n : ℕ) (hkn : k < n) :
    g^k • w∈(periodicPath T hA g p n).support := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hk : k < n
    · exact periodicPath_support_step T hA g p n (ih hk)
    · have he : k=n := by omega
      subst k
      exact periodicPath_translate_mem T hA g p hw n

lemma periodicPath_vertex_mem (g : G) {x : V} (p : T.Walk x (g • x))
    (k n : ℕ) (hkn : k ≤ n) : g^k • x∈(periodicPath T hA g p n).support := by
  rcases lt_or_eq_of_le hkn with h|h
  · exact periodicPath_translate_mem_of_lt T hA g p p.start_mem_support k n h
  · subst k
    exact (periodicPath T hA g p n).end_mem_support

lemma periodicPath_snd (g : G) {x : V} (p : T.Walk x (g • x))
    (hpn : ¬p.Nil) (n : ℕ) : (periodicPath T hA g p (n+1)).snd=p.snd := by
  induction n with
  | zero =>
    change (periodicPath T hA g p (0+1)).getVert 1=p.getVert 1
    simp only [periodicPath,nil_copy_append,SimpleGraph.Walk.getVert_copy,
      SimpleGraph.Walk.getVert_map,pow_zero]
    exact one_smul G (p.getVert 1)
  | succ n ih =>
    change (periodicPath T hA g p (n+1+1)).getVert 1=p.snd
    rw [periodicPath,SimpleGraph.Walk.getVert_copy]
    have hn : ¬(periodicPath T hA g p (n+1)).Nil := by
      intro hn
      have hl := hn.length_eq_zero
      rw [periodicPath_length] at hl
      have hpos : 0 < p.length := Nat.pos_of_ne_zero (fun he => hpn (SimpleGraph.Walk.length_eq_zero_iff.mp he))
      exact (Nat.mul_pos (Nat.succ_pos n) hpos).ne' hl
    exact (first_append_nonempty T _ _ hn).trans ih

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
