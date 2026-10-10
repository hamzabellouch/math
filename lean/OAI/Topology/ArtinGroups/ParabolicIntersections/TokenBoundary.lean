import OAI.Topology.ArtinGroups.ParabolicIntersections.CoefficientPaths
import OAI.Topology.ArtinGroups.Quivers.TokenTestVector
import OAI.Topology.ArtinGroups.Complexes.GeneratorTokenTest

namespace OAI

/-! Exact vertex tests express a generator through incoming coefficients. -/
namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A : Type} (Q : ReversibleQuiver V A) [Fintype V] [Fintype A]
  {I : Type} [Fintype I]

/-- A boundary for the token of a generator, retaining the precise source
level and cochain support. This is the first step of Lemma 7.3. -/
theorem generator_token_boundary (E : BasedComplex Q (K := ℂ) I) (hE : E.IsMinimal Q)
    (i : I) (hex : ScalarExactAt Q (E.testComplex Q (E.placement i).color)
      (E.placement i).color ((E.placement i).level + 2) (E.placement i).cochain) :
    ∃ y : TestIndex Q E.placement (E.placement i).color → ℂ,
      (∀ u, y u ≠ 0 → (E.placement u.1).cochain = (E.placement i).cochain - 1 ∧
        (E.placement u.1).level + Path.length u.2.val = (E.placement i).level + 1) ∧
      ∀ j : I, (Pi.single i (1 : ℂ) : I → ℂ) j =
        ∑ u, y u * pathCoordinates Q (E.differential u.1 j) (Path.dual Q u.2.val) := by
  let α := (E.placement i).color
  let T := E.testComplex Q α
  let t := generatorTokenTest Q E i
  let x : TestIndex Q E.placement α → ℂ := Pi.single t 1
  have hxs : ScalarSupported Q T ((E.placement i).level+2) (E.placement i).cochain x := by
    intro u hu
    apply Pi.single_eq_of_ne
    intro he
    subst u
    apply hu
    constructor
    · change (E.placement i).cochain + ((E.placement i).internal + 2) =
        (E.placement i).cochain + (E.placement i).internal + 2
      omega
    · rfl
  have hxd : Matrix.vecMul x (T.differential.map (vertexHom Q α)) = 0 := by
    rw [testComplex_vertex_differential Q E α]
    funext u
    change (∑ v, x v * testMatrix Q E.placement E.placement α E.differential v u) = 0
    rw [Finset.sum_eq_single t]
    · exact mul_eq_zero.mpr (Or.inr (test_token_row_zero Q E hE α t u rfl))
    · intro v _ hv
      rw [show x v = 0 from Pi.single_eq_of_ne hv _, MulZeroClass.zero_mul]
    · simp
  obtain ⟨y, hy, hd⟩ := hex x hxs hxd
  refine ⟨y, ?_, ?_⟩
  · intro u hu
    have hh := not_not.mp (fun h => hu (hy u h))
    change (E.placement u.1).cochain + ((E.placement u.1).internal + Path.length u.2.val) =
        (E.placement i).level+2-1 ∧
      (E.placement u.1).cochain = (E.placement i).cochain-1 at hh
    exact ⟨hh.2, by dsimp only [GeneratorPlacement.level] at *; omega⟩
  · intro j
    by_cases hj : (E.placement j).color = α
    · let s : TestIndex Q E.placement α := ⟨j, .inr (.inr α), rfl, hj.symm⟩
      have hh := congrFun hd s
      rw [testComplex_vertex_differential Q E α] at hh
      have he : x s = (Pi.single i (1 : ℂ) : I → ℂ) j := by
        dsimp only [x]
        by_cases hji : j = i
        · subst j
          have hs : s = t := by rfl
          rw [hs]
          simp only [Pi.single_eq_same]
        · rw [Pi.single_eq_of_ne hji]
          apply Pi.single_eq_of_ne
          intro he
          exact hji (congrArg (fun z : TestIndex Q E.placement α => z.1) he)
      rw [he] at hh
      rw [← hh]
      apply Finset.sum_congr rfl
      intro u _
      congr 1
      change (pathBasis Q u.2.val * E.differential u.1 j).token α = _
      exact token_path_mul Q u.2 _
    · have hji : j ≠ i := fun he => hj (by subst j; rfl)
      rw [Pi.single_eq_of_ne hji]
      symm
      apply Finset.sum_eq_zero
      intro u _
      have hz : pathCoordinates Q (E.differential u.1 j) (Path.dual Q u.2.val) = 0 := by
        by_contra hn
        have hc := coordinates_corner Q (E.entries.1 u.1 j) (E.entries.2 u.1 j) hn
        have ht : ReversibleQuiver.Path.target Q (Path.dual Q u.2.val) = α := by
          rw [Path.target_dual]
          exact u.2.property.1
        exact hj (hc.2.symm.trans ht)
      rw [hz, MulZeroClass.mul_zero]

end HarmonicArtin.ParabolicIntersections

end OAI
