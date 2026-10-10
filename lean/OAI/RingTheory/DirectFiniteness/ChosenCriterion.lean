import OAI.RingTheory.DirectFiniteness.FiniteGeneration

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.ChosenCriterion
open AssignedDevelopment CharacterIdempotents
variable {K V F m : Type} [Field K] [CharP K 2]
variable [Fintype V] [Fintype F] [Fintype m]
variable (ℓ : ℕ) [Fact ℓ.Prime]

local instance modulusNeZero : NeZero ℓ := inferInstance

variable (Inc : F → Finset V)
variable (assign : ∀ v, {f : F // v ∈ Inc f} ≃ Option (ZMod ℓ))
variable (hInc : ∀ f, (Inc f).Nonempty)
variable (hg : 12 ≤ (Planar.incidenceGraph (fun v f => v ∈ Inc f)).egirth)
variable (v₀ : V) (α : V → GluedGroup.PointGroup ℓ →* Multiplicative (ZMod ℓ))

abbrev inclusion := point Inc ℓ assign
abbrev inclusion_injective := point_injective Inc ℓ assign hInc hg
abbrev Extension := CharacterTwist.L (inclusion ℓ Inc assign)
  (inclusion_injective ℓ Inc assign hInc hg) v₀ α
abbrev Group := Extension ℓ Inc assign hInc hg v₀ α ×
  FiniteBlock.Auxiliary m (Multiplicative (ZMod ℓ))

variable {ζ : K} (hζ : IsPrimitiveRoot ζ ℓ) (X : Matrix m V K)
variable (i₀ : m) (slot : V → m)

def aOut : MonoidAlgebra K (Group (m := m) ℓ Inc assign hInc hg v₀ α) :=
  FiniteBlock.output (CoordinateCharacters.cyclicCharacter ℓ hζ) i₀
    (CharacterTwist.aMatrix (inclusion ℓ Inc assign) (inclusion_injective ℓ Inc assign hInc hg)
      v₀ α (CoordinateCharacters.cyclicCharacter ℓ hζ) X slot)

def bOut : MonoidAlgebra K (Group (m := m) ℓ Inc assign hInc hg v₀ α) :=
  FiniteBlock.output (CoordinateCharacters.cyclicCharacter ℓ hζ) i₀
    (CharacterTwist.bMatrix (inclusion ℓ Inc assign) (inclusion_injective ℓ Inc assign hInc hg)
      v₀ α (CoordinateCharacters.cyclicCharacter ℓ hζ) X slot)

include hζ in
lemma products (hodd : Odd ℓ)
    (hlt : Fintype.card m < Fintype.card V)
    (hglobal : X * X.transpose = -1)
    (hlocal : ∀ f i j, ∑ v ∈ Inc f, X i v * X j v = 0)
    (hα : ∀ v w, v ≠ w → slot v = slot w → α v ≠ α w) :
    aOut ℓ Inc assign hInc hg v₀ α hζ X i₀ slot *
      bOut ℓ Inc assign hInc hg v₀ α hζ X i₀ slot=1 ∧
    bOut ℓ Inc assign hInc hg v₀ α hζ X i₀ slot *
      aOut ℓ Inc assign hInc hg v₀ α hζ X i₀ slot≠1 := by
  let A := GluedGroup.PointGroup ℓ
  let C := Multiplicative (ZMod ℓ)
  let N := Base Inc ℓ assign
  let ι := point Inc ℓ assign
  let hi := point_injective Inc ℓ assign hInc hg
  let ξ := CoordinateCharacters.cyclicCharacter ℓ hζ
  have hξ : Function.Injective ξ := CoordinateCharacters.cyclicCharacter_injective ℓ hζ
  have hξ1 : ξ ≠ 1 := CoordinateCharacters.cyclicCharacter_ne_one ℓ hζ
  have hell : (ℓ : K) = 1 := natCast_eq_one_of_odd_of_two_eq_zero hodd CharTwo.two_eq_zero
  have hAc : (Fintype.card A : K) = 1 := by simp [A, GluedGroup.PointGroup, hell]
  have hCc : (Fintype.card C : K) = 1 := by simp [C, hell]
  let L := CharacterTwist.L ι hi v₀ α
  let f : MonoidAlgebra K N →ₐ[K] MonoidAlgebra K L :=
    MonoidAlgebra.mapDomainAlgHom K K ((CharacterTwist.emb ι hi v₀ α).comp (MonoidHom.inl N C))
  let lineSum (l : F) : MonoidAlgebra K L :=
    f (∑ c : C, MonoidAlgebra.single (line Inc ℓ assign hInc l c) 1)
  have hdec (v : V) : CharacterTwist.P (K := K) ι hi v₀ α v =
      1 + ∑ l : {l : F // v ∈ Inc l}, (lineSum l.val - 1) := by
    have hd := congrArg f (subgroup_decomposition (K := K) Inc ℓ assign hInc v)
    have hp : CharacterTwist.P (K := K) ι hi v₀ α v =
        f (∑ a : A, MonoidAlgebra.single (ι v a) 1) := by
      simp [CharacterTwist.P, pushed_eq_sum, f, CharacterTwist.localHom, hell]
      apply Fintype.sum_equiv (Equiv.refl A)
      intro a
      rfl
    rw [hp]
    simpa only [map_add, map_one, map_sum, map_sub, lineSum] using hd
  have hglobal' : X * X.transpose = 1 := by
    rw [hglobal]
    ext i j
    exact CharTwo.neg_eq _
  obtain ⟨ha,hb⟩ := CharacterTwist.matrix_products ι hi v₀ α ξ X Inc lineSum
    hdec hglobal' hlocal hlt (hAc ▸ one_ne_zero) (hCc ▸ one_ne_zero) slot hξ hα
  have hc : (Fintype.card (m → C) : K) ≠ 0 := by simp [hCc]
  exact FiniteBlock.output_products ξ i₀ hc hξ1 _ _ ha hb

instance groupFG : _root_.Group.FG (Group (m := m) ℓ Inc assign hInc hg v₀ α) := by
  have : _root_.Group.FG (Base Inc ℓ assign) :=
    _root_.Group.fg_of_surjective (PresentedGroup.mk_surjective _)
  have : _root_.Group.FG (Extension ℓ Inc assign hInc hg v₀ α) := multipleHNN_fg _ _ _
  infer_instance

end KaplanskyCounterexample.ChosenCriterion
end

end OAI
