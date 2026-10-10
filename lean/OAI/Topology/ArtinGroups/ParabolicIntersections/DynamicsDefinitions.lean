import OAI.Topology.ArtinGroups.ParabolicIntersections.Basic
import Mathlib.Topology.MetricSpace.Isometry

namespace OAI

/-!
# Acylindrical actions and visual splittings

The definitions below spell out the metric content of acylindrical
hyperbolicity. Non-elementarity means that an orbit has three distinct
Gromov-boundary limit points, represented by Gromov sequences whose
pairwise mixed products are bounded. No dynamical assertion is built
into a definition of an Artin group.
-/
namespace HarmonicArtin.ParabolicIntersections

noncomputable def gromovProduct {X : Type} [MetricSpace X] (o x y : X) : ℝ :=
  (dist o x + dist o y - dist x y)/2

def IsGromovHyperbolic (X : Type) [MetricSpace X] : Prop :=
  ∃ δ : ℝ, 0 ≤ δ ∧ ∀ o x y z : X,
    min (gromovProduct o x y) (gromovProduct o y z) ≤ gromovProduct o x z + δ

def IsGeodesicMetric (X : Type) [MetricSpace X] : Prop :=
  ∀ x y : X, ∃ γ : Set.Icc (0 : ℝ) (dist x y) → X,
    Isometry γ ∧ γ ⟨0,le_rfl,dist_nonneg⟩=x ∧ γ ⟨dist x y,dist_nonneg,le_rfl⟩=y

def IsGromovSequence {X : Type} [MetricSpace X] (o : X) (u : ℕ → X) : Prop :=
  ∀ R : ℝ, ∃ N : ℕ, ∀ m, N ≤ m → ∀ n, N ≤ n → R ≤ gromovProduct o (u m) (u n)

def IsAcylindrical (G X : Type) [Group G] [MetricSpace X] [MulAction G X] : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∃ N : ℕ, ∀ x y : X, R ≤ dist x y →
    {g : G | dist x (g • x) ≤ ε ∧ dist y (g • y) ≤ ε}.Finite ∧
      {g : G | dist x (g • x) ≤ ε ∧ dist y (g • y) ≤ ε}.ncard ≤ N

def HasThreeOrbitLimitPoints (G X : Type) [Group G] [MetricSpace X] [MulAction G X] : Prop :=
  ∃ o : X, ∃ u : Fin 3 → ℕ → G,
    (∀ i, IsGromovSequence o (fun n => u i n • o)) ∧
    ∀ i j, i ≠ j → ∃ B : ℝ, ∀ m n, gromovProduct o (u i m • o) (u j n • o) ≤ B

/-- An isometric non-elementary acylindrical action on a geodesic
Gromov-hyperbolic metric space. -/
def AcylindricallyHyperbolic (G : Type) [Group G] : Prop :=
  ∃ (X : Type) (metric : MetricSpace X) (action : MulAction G X),
    @IsGeodesicMetric X metric ∧ @IsGromovHyperbolic X metric ∧
    (∀ g : G, @Isometry X X metric.toPseudoMetricSpace.toPseudoEMetricSpace metric.toPseudoMetricSpace.toPseudoEMetricSpace
      (fun x => @SMul.smul G X action.toSMul g x)) ∧
    @IsAcylindrical G X _ metric action ∧ @HasThreeOrbitLimitPoints G X _ metric action

def WeaklyMalnormal {G : Type} [Group G] (P : Subgroup G) : Prop :=
  ∃ g : G, (↑(P ⊓ conjugate g P) : Set G).Finite

variable {S : Type} (M : CoxeterMatrix S)

/-- No nontrivial partition has every cross label equal to two. -/
def IsIrreducible : Prop :=
  ∀ Y : Set S, Y.Nonempty → Yᶜ.Nonempty → ∃ s ∈ Y, ∃ t ∉ Y, M s t ≠ 2

/-- The presentation-graph condition in CMMW Definition 2.4. The vertex
subgraphs are proper, cover every vertex, and omit no finite-label edge. -/
def IsVisualSplit (Y Z : Set S) : Prop :=
  Y ∪ Z = Set.univ ∧ Y ⊂ Set.univ ∧ Z ⊂ Set.univ ∧
    ∀ s ∈ Y \ Z, ∀ t ∈ Z \ Y, M s t = 0

lemma infinite_pair_visual_split (s t : S) (hst : s ≠ t) (hlabel : M s t=0) :
    IsVisualSplit M {s}ᶜ {t}ᶜ := by
  refine ⟨?_,?_,?_,?_⟩
  · ext a
    simp only [Set.mem_union,Set.mem_compl_iff,Set.mem_singleton_iff,Set.mem_univ,iff_true]
    by_cases ha : a=s
    · exact Or.inr (by simpa [ha] using hst)
    · exact Or.inl ha
  · apply Set.ssubset_univ_iff.mpr
    intro h
    have hs : s ∈ ({s}ᶜ : Set S) := h.symm ▸ Set.mem_univ s
    simp at hs
  · apply Set.ssubset_univ_iff.mpr
    intro h
    have ht : t ∈ ({t}ᶜ : Set S) := h.symm ▸ Set.mem_univ t
    simp at ht
  · intro a ha b hb
    have hat : a=t := by simpa using ha.2
    have hbs : b=s := by simpa using hb.2
    subst a
    subst b
    rw [M.symmetric]
    exact hlabel

end HarmonicArtin.ParabolicIntersections

end OAI
