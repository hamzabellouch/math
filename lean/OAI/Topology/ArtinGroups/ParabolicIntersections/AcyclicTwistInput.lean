import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedFamily
import OAI.Topology.ArtinGroups.Harmonic.UnfoldedInclusion

namespace OAI

/-!
# The published acyclic-evaluation input

Seidel--Thomas, *Braid group actions on derived categories of coherent
sheaves*, Duke Math. J. 108 (2001), Definition 2.5 (equation (2.2)),
and the first sentence of the proof of Proposition 2.12:
https://arxiv.org/pdf/math/0001043, pp. 13 and 17.
A twist is the cone of evaluation. If the entire evaluated Hom complex
is acyclic, this cone is isomorphic to the original object. For bounded
projective complexes the resulting isomorphism is a homotopy equivalence.
Below is precisely this standard consequence in the existing vertex-test
notation. It is independent of the Artin stabilizer argument.
-/
namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
attribute [local instance] Classical.decEq Classical.propDecidable

structure PublishedAcyclicTwist {V A : Type} (Q : ReversibleQuiver V A)
    [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A] : Prop where
  fix_of_exact : ∀ (x : FiniteHomotopyClass Q (K := ℂ)) (α : V),
    (∀ l c, ClassTestExact Q α l c x) → classPositiveTwist Q α x=x

variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (f : S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "hd" => coxeterFusionEdge_symm M
local notation "diag" => coxeterFusionEdge_diag M
local notation "Q" => fusionQuiver m d hd

/-- Acyclic tests make every generator, and hence the entire standard
parabolic, fix the actual pointed family. -/
theorem pointed_standard_fixes_of_acyclic_tests (hAcyclic : PublishedAcyclicTwist Q)
    (Y : Set S) (x : Artin M)
    (h : ∀ H, ∀ α ∈ Set.range (unfoldedInclusion M Y), ∀ l c,
      ClassTestExact Q α l c (pointedFamily M f x H))
    (g : Artin M) (hg : g ∈ artinParabolic M Y) :
    pointedFamily M f (g*x)=pointedFamily M f x := by
  have hgen (i : S) (hi : i ∈ Y) (H : PointedLabel M) :
      pointedAction M (generator M i) (pointedFamily M f x H)=pointedFamily M f x H := by
    rw [pointedAction_generator, fusionPacketPerm, ← classPacketPerm_toList]
    have hl (w : List (FusionLabel m)) :
        (w.map (fun L => classTwistPerm Q (fusionQuiver_no_loops m d hd diag)
          (.inl i,L))).prod (pointedFamily M f x H)=pointedFamily M f x H := by
      induction w with
      | nil => rfl
      | cons L w ih =>
        change classPositiveTwist Q (.inl i,L)
          ((w.map (fun L => classTwistPerm Q (fusionQuiver_no_loops m d hd diag)
            (.inl i,L))).prod (pointedFamily M f x H))=_
        rw [ih]
        exact hAcyclic.fix_of_exact _ _ (h H _ ⟨(⟨i,hi⟩,L),rfl⟩)
    exact hl _
  funext H
  change pointedAction M (g*x) (pointedInitial M f H)=_
  rw [map_mul, Equiv.Perm.mul_apply]
  change pointedAction M g (pointedFamily M f x H)=_
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨i,hi,rfl⟩ := hg
    exact hgen i hi H
  | one => rw [map_one]; rfl
  | mul a b _ _ ha hb => simp only [map_mul, Equiv.Perm.mul_apply, hb,ha]
  | inv a _ ha =>
    rw [map_inv]
    apply (pointedAction M a).injective
    change (pointedAction M a) ((pointedAction M a).symm _) = _
    rw [Equiv.apply_symm_apply,ha]

end HarmonicArtin.ParabolicIntersections

end OAI
