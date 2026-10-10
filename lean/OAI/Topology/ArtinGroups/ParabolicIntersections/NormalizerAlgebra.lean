import OAI.Topology.ArtinGroups.ParabolicIntersections.Basic

namespace OAI

/-! Normalizing a subgroup can be tested outside any proper subgroup. -/
namespace HarmonicArtin.ParabolicIntersections
variable {G : Type*} [Group G]

lemma conjugate_eq_map (g : G) (P : Subgroup G) :
    conjugate g P=P.map (MulAut.conj g).toMonoidHom := by
  ext x
  rw [mem_conjugate,Subgroup.mem_map_equiv]
  rfl

lemma mem_normalizer_iff_conjugate (g : G) (P : Subgroup G) :
    g∈Subgroup.normalizer (P : Set G) ↔ conjugate g P=P := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change (P.map (MulAut.conj g).toMonoidHom=P) ↔ _
  rw [←conjugate_eq_map]

lemma le_normalizer_of_outside (P K C : Subgroup G)
    (ha : ∃ a : G, a∈K ∧ a∉C)
    (hn : ∀ g : G, g∈K → g∉C → conjugate g P=P) :
    K≤Subgroup.normalizer (P : Set G) := by
  obtain ⟨a,ha,haC⟩ := ha
  have haN := (mem_normalizer_iff_conjugate a P).mpr (hn a ha haC)
  intro g hg
  by_cases hgC : g∈C
  · have hgaC : g*a∉C := by
      intro h
      exact haC (by simpa only [inv_mul_cancel_left] using C.mul_mem (C.inv_mem hgC) h)
    have hgaN := (mem_normalizer_iff_conjugate (g*a) P).mpr (hn (g*a) (K.mul_mem hg ha) hgaC)
    have h := (Subgroup.normalizer (P : Set G)).mul_mem hgaN
      ((Subgroup.normalizer (P : Set G)).inv_mem haN)
    simpa only [mul_inv_cancel_right] using h
  · exact (mem_normalizer_iff_conjugate g P).mpr (hn g hg hgC)

end HarmonicArtin.ParabolicIntersections

end OAI
