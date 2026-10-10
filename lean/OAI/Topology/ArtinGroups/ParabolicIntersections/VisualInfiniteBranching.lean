import OAI.Topology.ArtinGroups.ParabolicIntersections.VisualFactorMalnormal
import OAI.Topology.ArtinGroups.ParabolicIntersections.GeneratorPowers

namespace OAI

/-! Infinite branching for the genuine visual tree. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable

private lemma injective_zpow_orbit {G V : Type} [Group G] [MulAction G V]
    (a : G) (v : V) (ha : ∀ n : ℤ, n≠0 → a^n∉MulAction.stabilizer G v) :
    Function.Injective (fun n : ℤ => a^n • v) := by
  intro m n he
  change a^m • v=a^n • v at he
  by_contra hmn
  have hn : -m+n≠0 := by omega
  apply ha (-m+n) hn
  change a^(-m+n) • v=v
  rw [zpow_add,mul_smul,←he,zpow_neg,inv_smul_smul]

variable {S : Type} [Fintype S] (M : CoxeterMatrix S) (Y Z : Set S)
variable [hSplit : Fact (IsVisualSplit M Y Z)]
noncomputable local instance : MulAction (Artin M) (VisualVertex M Y Z) :=
  visualAction M Y Z hSplit.out

/-- Every oriented edge belongs to an infinite orbit under the stabilizer
of its initial vertex. In particular, the visual tree is not a line. -/
theorem visual_infinite_branching {u v : VisualVertex M Y Z}
    (h : (visualGraph M Y Z).Adj u v) :
    ∃ a : Artin M, a∈MulAction.stabilizer (Artin M) u ∧
      Function.Injective (fun n : ℤ => a^n • v) := by
  obtain ⟨g,hu,hv⟩ := visual_adj_representatives M Y Z h
  have hside : visualSide Y Z v.1≠Set.univ := by
    cases v.1
    · exact (Set.ssubset_iff_subset_ne.mp hSplit.out.2.1).2
    · exact (Set.ssubset_iff_subset_ne.mp hSplit.out.2.2.1).2
  obtain ⟨t,ht⟩ := Set.nonempty_compl.mpr hside
  have hgen : generator M t∈artinParabolic M (visualSide Y Z u.1) := by
    apply (generator_mem_standard_iff M _ _).mpr
    have hcover : visualSide Y Z u.1 ∪ visualSide Y Z v.1=Set.univ := by
      have hne := h.1
      cases hu' : u.1 <;> cases hv' : v.1
      · exact False.elim (hne (hu'.trans hv'.symm))
      · exact hSplit.out.1
      · exact Set.union_comm Y Z ▸ hSplit.out.1
      · exact False.elim (hne (hu'.trans hv'.symm))
    exact (hcover.symm ▸ Set.mem_univ t : t∈visualSide Y Z u.1 ∪ visualSide Y Z v.1).resolve_right ht
  let a := g*generator M t*g⁻¹
  have hapow (n : ℤ) : a^n=g*(generator M t)^n*g⁻¹ := by
    exact (map_zpow (MulAut.conj g).toMonoidHom (generator M t) n).symm
  refine ⟨a,?_,injective_zpow_orbit a v ?_⟩
  · rw [hu,visual_vertex_stabilizer,mem_conjugate]
    have he : g⁻¹*a*g=generator M t := by dsimp only [a]; group
    rw [he]
    exact hgen
  · intro n hn hm
    rw [hv,visual_vertex_stabilizer,mem_conjugate,hapow] at hm
    have he : g⁻¹*(g*generator M t^n*g⁻¹)*g=generator M t^n := by group
    rw [he] at hm
    exact generator_zpow_not_mem M (visualSide Y Z v.1) t ht n hn hm

end HarmonicArtin.ParabolicIntersections

end OAI
