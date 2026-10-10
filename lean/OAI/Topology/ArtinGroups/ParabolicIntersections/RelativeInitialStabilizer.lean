import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedInitialStabilizer
import OAI.Topology.ArtinGroups.ParabolicIntersections.RelativeFamily

namespace OAI

/-!
# The initial stabilizer in the relative diagram

The sole input below is the unrestricted standard-parabolic embedding theorem:
van der Lek, *The Homotopy Type of Complex Hyperplane Complements* (1983),
Chapter II, §4, Theorem 4.13(i). See also Charney–Paris, *Convexity of parabolic
subgroups in Artin groups* (2014), §1, p. 2, https://arxiv.org/abs/1401.7634.
The exact case needed is injectivity of the canonical inclusion from the
original Artin presentation into the presentation with one additional color.
The categorical stabilizer identity is proved below, not assumed.
-/
namespace HarmonicArtin.ParabolicIntersections
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (X:Set S)
local instance : LinearOrder (S⊕Unit) := Sum.Lex.linearOrder
local notation "N" => relativeMatrix M X
attribute [local instance] Classical.decEq Classical.propDecidable

structure VanDerLekRelativeEmbedding : Prop where
  injective : Function.Injective (relativeArtinHom M X)

omit [Fintype S] [LinearOrder S] in
lemma relativeFrame_commuting_type :
    {i:S⊕Unit | i∈Set.range (Sum.inl:S→S⊕Unit) ∧ N i (.inr ())=2} = Sum.inl '' X := by
  ext i
  cases i with
  | inl s =>
    by_cases hs:s∈X <;> simp [relativeMatrix_frame,hs]
  | inr u => simp

/-- Proposition 8.3, conditional only on the published embedding input. -/
theorem relative_initial_stabilizer (hEmb:VanDerLekRelativeEmbedding M X) :
    MulAction.stabilizer (Artin M) (relativeInitial M X) = artinParabolic M X := by
  apply le_antisymm
  · intro a ha
    have hfix:pointedFamily N (.inr ()) (relativeArtinHom M X a)=pointedFamily N (.inr ()) 1 := by
      change a • relativeInitial M X=relativeInitial M X at ha
      funext L
      have h:=congrFun ha L
      change pointedAction N (relativeArtinHom M X a) (pointedInitial N (.inr ()) L)=_ at h
      simpa only [pointedFamily,map_one,Equiv.Perm.one_apply,relativeInitial] using h
    have hmap:relativeArtinHom M X a∈artinParabolic N (Set.range (Sum.inl:S→S⊕Unit)):=by
      have he:=relativeArtinHom_parabolic M X Set.univ
      simp only [Set.image_univ] at he
      rw [←he]
      exact ⟨a,by rw [standard_univ];trivial,rfl⟩
    have hm:=pointed_initial_stabilizer_le N (.inr ()) (Set.range (Sum.inl:S→S⊕Unit))
      (by simp) (relativeArtinHom M X a) hmap hfix
    rw [relativeFrame_commuting_type M X,←relativeArtinHom_parabolic M X X] at hm
    obtain ⟨b,hb,he⟩:=hm
    exact hEmb.injective he ▸ hb
  · exact standard_le_relative_stabilizer M X

end HarmonicArtin.ParabolicIntersections

end OAI
