import OAI.Topology.ArtinGroups.ParabolicIntersections.UnconditionalMain

namespace OAI

/-! Rank descent gives a minimal member of every nonempty family of parabolics. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)

/-- A nonempty family of parabolic subgroups has an inclusion-minimal member.
The argument follows the size of a displayed defining type and does not
assume that rank is conjugacy invariant. -/
theorem exists_minimal_parabolic (F : Set (Subgroup (Artin M))) (hF : F.Nonempty)
    (hpar : ∀ P∈F, IsParabolic M P) :
    ∃ P∈F, ∀ Q∈F, Q≤P → Q=P := by
  have hex : ∃ n : ℕ, ∃ (X : Set S) (g : Artin M),
      conjugate g (artinParabolic M X)∈F ∧ X.ncard=n := by
    obtain ⟨P,hP⟩ := hF
    obtain ⟨X,g,rfl⟩ := hpar P hP
    exact ⟨X.ncard,X,g,hP,rfl⟩
  obtain ⟨X,g,hX,hcard⟩ := Nat.find_spec hex
  refine ⟨conjugate g (artinParabolic M X),hX,?_⟩
  intro Q hQ hle
  by_contra hne
  obtain ⟨Z,c,hZX,hc,he⟩ := inside_conjugate M (unconditional_inside_intersection M)
    X g (hpar Q hQ)
  rw [inf_eq_right.mpr hle] at he
  have hZX' : Z≠X := by
    intro h
    rw [h,conjugate_mul,conjugate_eq_self hc] at he
    exact hne he
  have hlt : Z.ncard<Nat.find hex := by
    rw [←hcard]
    exact Set.ncard_lt_ncard (ssubset_of_subset_of_ne hZX hZX')
  have hmin := Nat.find_min' hex (show ∃ (D : Set S) (a : Artin M),
      conjugate a (artinParabolic M D)∈F ∧ D.ncard=Z.ncard from
    ⟨Z,g*c,he ▸ hQ,rfl⟩)
  omega

end HarmonicArtin.ParabolicIntersections

end OAI
