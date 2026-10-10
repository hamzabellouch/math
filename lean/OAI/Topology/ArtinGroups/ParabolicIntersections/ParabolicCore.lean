import OAI.Topology.ArtinGroups.ParabolicIntersections.UnconditionalMain
import OAI.Topology.ArtinGroups.ParabolicIntersections.NormalParabolic

namespace OAI

/-! The normal core of every proper parabolic in irreducible type is trivial.
The arbitrary-intersection theorem also supplies a finite list of conjugates
realizing this core. These are the algebraic inputs to the tree argument. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable

variable {G : Type*} [Group G]

lemma normalCore_eq_sInf_conjugates (P : Subgroup G) :
    P.normalCore=sInf (Set.range (fun g : G => conjugate g P)) := by
  rw [sInf_range]
  ext x
  simp only [Subgroup.mem_iInf,mem_conjugate]
  change (∀ g : G, g*x*g⁻¹∈P) ↔ ∀ g : G, g⁻¹*x*g∈P
  constructor <;> intro h g <;> simpa only [inv_inv] using h g⁻¹

variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)

omit [LinearOrder S] in
/-- The conjugate form of CMMW Lemma 3.3. -/
theorem normal_parabolic (hIrred : IsIrreducible M)
    (P : Subgroup (Artin M)) (hP : IsParabolic M P) (hn : P.Normal) :
    P=⊥ ∨ P=⊤ := by
  obtain ⟨X,g,rfl⟩ := hP
  have hn' : (conjugate g⁻¹ (conjugate g (artinParabolic M X))).Normal := by
    exact hn.comap (MulAut.conj (g⁻¹)⁻¹).toMonoidHom
  rw [conjugate_inv_cancel] at hn'
  rcases normal_standard_parabolic M hIrred X hn' with hx|hx
  · left
    simp [hx,artinParabolic]
  · right
    rw [hx,standard_univ,conjugate_top]

/-- No nontrivial normal subgroup obtained as a parabolic can lie in a
proper parabolic of an irreducible Artin group. -/
theorem parabolic_normalCore_eq_bot (hIrred : IsIrreducible M)
    (P : Subgroup (Artin M)) (hP : IsParabolic M P) (hproper : P≠⊤) :
    P.normalCore=⊥ := by
  have hC : IsParabolic M P.normalCore := by
    rw [normalCore_eq_sInf_conjugates]
    apply (unconditional_arbitrary_intersections M _ ?_).2
    rintro Q ⟨g,rfl⟩
    exact isParabolic_conjugate M hP g
  rcases normal_parabolic M hIrred P.normalCore hC inferInstance with h|h
  · exact h
  · exact False.elim (hproper (top_le_iff.mp (h ▸ P.normalCore_le)))

/-- A bounded finite family of conjugates has trivial intersection. This is
used to find a finite subtree with trivial pointwise stabilizer. -/
theorem finite_conjugates_inf_bot (hIrred : IsIrreducible M)
    (P : Subgroup (Artin M)) (hP : IsParabolic M P) (hproper : P≠⊤) :
    ∃ F : Finset (Subgroup (Artin M)),
      (∀ Q∈F, ∃ g : Artin M, Q=conjugate g P) ∧ F.card≤Nat.card S ∧
        sInf (↑F : Set (Subgroup (Artin M)))=⊥ := by
  obtain ⟨⟨F,hF,hcard,he⟩,_⟩ := unconditional_arbitrary_intersections M
    (Set.range (fun g : Artin M => conjugate g P)) (by
      rintro Q ⟨g,rfl⟩
      exact isParabolic_conjugate M hP g)
  refine ⟨F,?_,hcard,?_⟩
  · intro Q hQ
    obtain ⟨g,hg⟩ := hF hQ
    exact ⟨g,hg.symm⟩
  · rw [←he,←normalCore_eq_sInf_conjugates,parabolic_normalCore_eq_bot M hIrred P hP hproper]

end HarmonicArtin.ParabolicIntersections

end OAI
