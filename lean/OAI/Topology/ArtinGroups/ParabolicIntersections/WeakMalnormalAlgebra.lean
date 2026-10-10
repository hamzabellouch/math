import OAI.Topology.ArtinGroups.ParabolicIntersections.DynamicsDefinitions

namespace OAI

/-! Conjugation and subgroup facts about weak malnormality. -/
namespace HarmonicArtin.ParabolicIntersections
variable {G : Type} [Group G]

lemma weaklyMalnormal_of_conjugates_inf_bot (P : Subgroup G) (g h : G)
    (he : conjugate g P ⊓ conjugate h P=⊥) : WeaklyMalnormal P := by
  have he' := congrArg (conjugate g⁻¹) he
  rw [conjugate_inf,conjugate_inv_cancel,←conjugate_mul,conjugate_bot] at he'
  refine ⟨g⁻¹*h,?_⟩
  rw [he']
  exact Set.finite_singleton 1

lemma WeaklyMalnormal.mono {P Q : Subgroup G} (hQ : WeaklyMalnormal Q) (hle : P≤Q) :
    WeaklyMalnormal P := by
  obtain ⟨g,hg⟩ := hQ
  exact ⟨g,hg.subset (inf_le_inf hle (conjugate_mono g hle))⟩

lemma WeaklyMalnormal.conjugate_subgroup {P : Subgroup G} (hP : WeaklyMalnormal P) (g : G) :
    WeaklyMalnormal (conjugate g P) := by
  obtain ⟨h,hh⟩ := hP
  refine ⟨g*h*g⁻¹,?_⟩
  have he : conjugate g P ⊓ conjugate (g*h*g⁻¹) (conjugate g P)=
      conjugate g (P ⊓ conjugate h P) := by
    rw [conjugate_inf,←conjugate_mul,←conjugate_mul]
    group
  rw [he]
  have him := hh.image (fun x : G => g*x*g⁻¹)
  apply him.subset
  intro x hx
  refine ⟨g⁻¹*x*g,(mem_conjugate _ _ _).mp hx,?_⟩
  group

end HarmonicArtin.ParabolicIntersections

end OAI
