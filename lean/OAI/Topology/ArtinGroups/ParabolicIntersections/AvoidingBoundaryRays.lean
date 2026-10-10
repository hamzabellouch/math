import OAI.Topology.ArtinGroups.ParabolicIntersections.AvoidingRealization
import OAI.Topology.ArtinGroups.ParabolicIntersections.TreeBoundaryRays
import OAI.Topology.ArtinGroups.ParabolicIntersections.TreePeriodicGrowth

namespace OAI

/-! Tree rays give three distinct orbit limit points in the genuine metric realization. -/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
open GraphRealization
variable {G V : Type} [Group G] [MulAction G V]
variable (T : SimpleGraph V) (u v : V)

lemma realization_orbit_product (H : SimpleGraph V) (hH : H.Connected)
    (hB : PreservesAdj (G := G) H) (x : V) (g h : G) :
    gromovProduct (vertex H hH x) (act H hB hH g (vertex H hH x))
      (act H hB hH h (vertex H hH x))=graphProduct H x (g • x) (h • x) := by
  rw [act_vertex,act_vertex]
  simp only [gromovProduct,graphProduct,dist_vertex]

theorem realization_three_rays (hT : T.IsTree) (hA : PreservesAdj (G := G) T)
    (hne : u≠v) (hnadj : ¬T.Adj u v)
    (x : V) (seq : Fin 3 → ℕ → G) (P : ∀ i n,T.Walk x (seq i n • x))
    (hP : ∀ i n,(P i n).IsPath) (hzero : ∀ i,(P i 0).Nil)
    (d : Fin 3 → V) (hd : Function.Injective d)
    (hfirst : ∀ i n,0 < n → (P i n).snd=d i)
    (hseq : ∀ (i : Fin 3) (R : ℝ), ∃ N : ℕ,∀ m,N ≤ m → ∀ n,N ≤ n →
      R ≤ graphProduct (avoidingGraph (G := G) T u v) x (seq i m • x) (seq i n • x)) :
    let H := avoidingGraph (G := G) T u v
    let hH := avoidingGraph_connected T u v hT hA hne hnadj
    let hB := avoidingGraph_preservesAdj T u v hA
    let _ := action H hB hH
    HasThreeOrbitLimitPoints G (Space H hH) := by
  let H := avoidingGraph (G := G) T u v
  have hH := avoidingGraph_connected T u v hT hA hne hnadj
  have hB := avoidingGraph_preservesAdj T u v hA
  let _ := action H hB hH
  refine ⟨vertex H hH x,seq,?_,?_⟩
  · intro i R
    obtain ⟨N,hN⟩ := hseq i R
    refine ⟨N,?_⟩
    intro m hm n hn
    change R ≤ gromovProduct (vertex H hH x) (act H hB hH (seq i m) (vertex H hH x))
      (act H hB hH (seq i n) (vertex H hH x))
    rw [realization_orbit_product]
    exact hN m hm n hn
  · intro i j hij
    refine ⟨1/2,?_⟩
    intro m n
    change gromovProduct (vertex H hH x) (act H hB hH (seq i m) (vertex H hH x))
      (act H hB hH (seq j n) (vertex H hH x)) ≤ 1/2
    rw [realization_orbit_product]
    apply separated_graphProduct T H hT hH (avoidingGraph_pathSaturated T u v hT.isAcyclic)
      (P i m) (P j n) (hP i m) (hP j n)
    by_cases hm : m=0
    · exact Or.inl (hm ▸ hzero i)
    by_cases hn : n=0
    · exact Or.inr (Or.inl (hn ▸ hzero j))
    refine Or.inr (Or.inr ?_)
    rw [hfirst i m (Nat.pos_of_ne_zero hm),hfirst j n (Nat.pos_of_ne_zero hn)]
    exact fun he => hij (hd he)

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
