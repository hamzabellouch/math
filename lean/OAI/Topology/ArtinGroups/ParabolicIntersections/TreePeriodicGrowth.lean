import OAI.Topology.ArtinGroups.ParabolicIntersections.TreePeriodicPaths
import OAI.Topology.ArtinGroups.ParabolicIntersections.TreeSegmentCount
import OAI.Topology.ArtinGroups.ParabolicIntersections.TreeShortcutHyperbolic

namespace OAI

/-! Periodic translates of a free segment give boundary points of the shortcut graph. -/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
attribute [local instance] Classical.decEq Classical.propDecidable
variable {G V : Type} [Group G] [MulAction G V]
variable (T : SimpleGraph V) (hA : PreservesAdj (G := G) T)
include hA

lemma periodic_powers_injective (hT : T.IsAcyclic) (g : G) {x : V}
    (p : T.Walk x (g • x)) (hp : p.IsPath) (hpn : ¬p.Nil)
    (hturn : p.reverse.snd≠g • p.snd) : Function.Injective (fun n : ℕ => g^n) := by
  intro m n he
  have hd := congrArg (fun a : G => T.dist x (a • x)) he
  rw [periodic_orbit_distance T hA hT g p hp hpn hturn m,
    periodic_orbit_distance T hA hT g p hp hpn hturn n] at hd
  have hpos : 0 < p.length := Nat.pos_of_ne_zero (fun hz => hpn (SimpleGraph.Walk.length_eq_zero_iff.mp hz))
  exact Nat.mul_right_cancel hpos hd

theorem periodic_occurrences (hT : T.IsAcyclic) (g : G) {x u v : V}
    (p : T.Walk x (g • x)) (hp : p.IsPath) (hpn : ¬p.Nil)
    (hturn : p.reverse.snd≠g • p.snd)
    (hfree : pairStabilizer (G := G) u v=⊥) (a : G)
    (hau : a • u∈p.support) (hav : a • v∈p.support) (n : ℕ) :
    n ≤ (segmentOccurrences (G := G) u v T (periodicPath T hA g p n)).ncard := by
  let f (k : Fin n) : G := g^k.val*a
  have hmem (k : Fin n) : f k∈segmentOccurrences (G := G) u v T (periodicPath T hA g p n) := by
    constructor
    · change (g^k.val*a) • u∈_
      rw [mul_smul]
      exact periodicPath_translate_mem_of_lt T hA g p hau k.val n k.isLt
    · change (g^k.val*a) • v∈_
      rw [mul_smul]
      exact periodicPath_translate_mem_of_lt T hA g p hav k.val n k.isLt
  have hinj : Function.Injective f := by
    intro i j he
    apply Fin.ext
    exact periodic_powers_injective T hA hT g p hp hpn hturn (mul_right_cancel he)
  have hc := Set.ncard_le_ncard_of_injOn (s := Set.univ) f (fun k _ => hmem k) hinj.injOn
    (segmentOccurrences_finite hfree T (periodicPath T hA g p n))
  simpa only [Set.ncard_univ,Nat.card_fin] using hc

theorem periodic_shortcut_growth (hT : T.IsTree) (u v : V)
    (hfree : pairStabilizer (G := G) u v=⊥) (hne : u≠v) (hnadj : ¬T.Adj u v)
    (g : G) {x : V} (p : T.Walk x (g • x)) (hp : p.IsPath) (hpn : ¬p.Nil)
    (hturn : p.reverse.snd≠g • p.snd) (a : G)
    (hau : a • u∈p.support) (hav : a • v∈p.support) (n : ℕ) :
    n ≤ (avoidingGraph (G := G) T u v).dist x (g^n • x)*(2*T.dist u v+1)^2 := by
  exact (periodic_occurrences T hA hT.isAcyclic g p hp hpn hturn hfree a hau hav n).trans
    (segmentOccurrences_bound_dist T u v hT hA hfree hne hnadj (periodicPath T hA g p n)
      (periodicPath_isPath T hA hT.isAcyclic g p hp hpn hturn n))

theorem periodic_shortcut_escape (hT : T.IsTree) (u v : V)
    (hfree : pairStabilizer (G := G) u v=⊥) (hne : u≠v) (hnadj : ¬T.Adj u v)
    (g : G) {x : V} (p : T.Walk x (g • x)) (hp : p.IsPath) (hpn : ¬p.Nil)
    (hturn : p.reverse.snd≠g • p.snd) (a : G)
    (hau : a • u∈p.support) (hav : a • v∈p.support) (R : ℝ) :
    ∃ N : ℕ,∀ n,N ≤ n → R ≤ ((avoidingGraph (G := G) T u v).dist x (g^n • x) : ℝ) := by
  let C := (2*T.dist u v+1)^2
  refine ⟨Nat.ceil (R*C),?_⟩
  intro n hn
  have hc : (0 : ℝ) < C := by dsimp only [C]; positivity
  have h₁ : R*C ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have h₂ : (n : ℝ) ≤ ((avoidingGraph (G := G) T u v).dist x (g^n • x) : ℝ)*C := by
    exact_mod_cast periodic_shortcut_growth T hA hT u v hfree hne hnadj g p hp hpn hturn a hau hav n
  exact (mul_le_mul_iff_left₀ hc).mp (by simpa only [mul_comm] using h₁.trans h₂)

theorem periodic_shortcut_gromov (hT : T.IsTree) (u v : V)
    (hfree : pairStabilizer (G := G) u v=⊥) (hne : u≠v) (hnadj : ¬T.Adj u v)
    (g : G) {x : V} (p : T.Walk x (g • x)) (hp : p.IsPath) (hpn : ¬p.Nil)
    (hturn : p.reverse.snd≠g • p.snd) (a : G)
    (hau : a • u∈p.support) (hav : a • v∈p.support) (R : ℝ) :
    ∃ N : ℕ,∀ m,N ≤ m → ∀ n,N ≤ n →
      R ≤ graphProduct (avoidingGraph (G := G) T u v) x (g^m • x) (g^n • x) := by
  let H := avoidingGraph (G := G) T u v
  have hH := avoidingGraph_connected T u v hT hA hne hnadj
  have hS := avoidingGraph_pathSaturated (G := G) T u v hT.isAcyclic
  obtain ⟨N,hN⟩ := periodic_shortcut_escape T hA hT u v hfree hne hnadj g p hp hpn hturn a hau hav (R+1)
  refine ⟨N,?_⟩
  have hordered (m n : ℕ) (hm : N ≤ m) (hmn : m ≤ n) :
      R ≤ graphProduct H x (g^m • x) (g^n • x) := by
    have h := shortcut_dist_split T H hT hH hS (periodicPath T hA g p n)
      (periodicPath_isPath T hA hT.isAcyclic g p hp hpn hturn n)
      (periodicPath_vertex_mem T hA g p m n hmn)
    have h' : (H.dist x (g^m • x) : ℝ)+H.dist (g^m • x) (g^n • x) ≤ H.dist x (g^n • x)+1 := by
      exact_mod_cast h
    have hd := hN m hm
    change R+1 ≤ (H.dist x (g^m • x) : ℝ) at hd
    unfold graphProduct
    linarith
  intro m hm n hn
  rcases le_total m n with h|h
  · exact hordered m n hm h
  · have he : graphProduct H x (g^m • x) (g^n • x)=graphProduct H x (g^n • x) (g^m • x) := by
      unfold graphProduct
      rw [H.dist_comm (u := g^m • x) (v := g^n • x)]
      ring
    rw [he]
    exact hordered n m hn h

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
