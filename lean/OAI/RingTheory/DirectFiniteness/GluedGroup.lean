import OAI.RingTheory.DirectFiniteness.WordReduction

namespace OAI

universe u_1 u_2

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.GluedGroup

variable {V : Type u_1} {F : Type u_2} (Inc : F → Finset V) (ℓ : ℕ)

abbrev Generator := F × {c : ZMod ℓ // c ≠ 0}

/-- Generators belonging to a prescribed local point group. -/
abbrev LocalGenerator (v : V) := {g : Generator (F := F) ℓ // v ∈ Inc g.1}

abbrev PointGroup := Multiplicative (Fin 2 → ZMod ℓ)

variable (incMap : ∀ v : V, {f : F // v ∈ Inc f} → (ZMod ℓ →+ (Fin 2 → ZMod ℓ)))

def localEvaluation (v : V) : FreeGroup (LocalGenerator Inc ℓ v) →* PointGroup ℓ :=
  FreeGroup.lift fun g => Multiplicative.ofAdd
    (incMap v ⟨g.val.1, g.property⟩ g.val.2.val)

def includeLocal (v : V) : FreeGroup (LocalGenerator Inc ℓ v) →*
    FreeGroup (Generator (F := F) ℓ) := FreeGroup.map Subtype.val

def relators : Set (FreeGroup (Generator (F := F) ℓ)) :=
  {w | ∃ v : V, ∃ r : FreeGroup (LocalGenerator Inc ℓ v),
    localEvaluation Inc ℓ incMap v r = 1 ∧ includeLocal Inc ℓ v r = w}

abbrev N := PresentedGroup (relators Inc ℓ incMap)

def fromLocal (v : V) : FreeGroup (LocalGenerator Inc ℓ v) →* N Inc ℓ incMap :=
  (PresentedGroup.mk (relators Inc ℓ incMap)).comp (includeLocal Inc ℓ v)

lemma local_kernel_le (v : V) : (localEvaluation Inc ℓ incMap v).ker ≤
    (fromLocal Inc ℓ incMap v).ker := by
  intro r hr
  exact PresentedGroup.one_of_mem ⟨v, r, hr, rfl⟩

/-- The direction partition covers every nonzero element of each point group. -/
def CoversPoints : Prop := ∀ (v : V) (a : Fin 2 → ZMod ℓ), a ≠ 0 →
  ∃ (f : F) (hf : v ∈ Inc f) (c : ZMod ℓ), c ≠ 0 ∧ incMap v ⟨f, hf⟩ c = a

lemma localEvaluation_surjective (hc : CoversPoints Inc ℓ incMap) (v : V) :
    Function.Surjective (localEvaluation Inc ℓ incMap v) := by
  intro a
  by_cases ha : a.toAdd = 0
  · refine ⟨1, ?_⟩
    simpa using congrArg Multiplicative.ofAdd ha.symm
  · obtain ⟨f, hf, c, hc, hca⟩ := hc v a.toAdd ha
    refine ⟨FreeGroup.of ⟨(f, ⟨c, hc⟩), hf⟩, ?_⟩
    simpa [localEvaluation] using congrArg Multiplicative.ofAdd hca

def theta (hc : CoversPoints Inc ℓ incMap) (v : V) : PointGroup ℓ →* N Inc ℓ incMap :=
  (localEvaluation Inc ℓ incMap v).liftOfSurjective
    (localEvaluation_surjective Inc ℓ incMap hc v)
    ⟨fromLocal Inc ℓ incMap v, local_kernel_le Inc ℓ incMap v⟩

lemma theta_localEvaluation (hc : CoversPoints Inc ℓ incMap) (v : V)
    (w : FreeGroup (LocalGenerator Inc ℓ v)) :
    theta Inc ℓ incMap hc v (localEvaluation Inc ℓ incMap v w) =
      fromLocal Inc ℓ incMap v w := by
  simp [theta]

lemma theta_generator (hc : CoversPoints Inc ℓ incMap) (v : V)
    (f : F) (hf : v ∈ Inc f) (c : ZMod ℓ) (hc0 : c ≠ 0) :
    theta Inc ℓ incMap hc v (Multiplicative.ofAdd (incMap v ⟨f, hf⟩ c)) =
      PresentedGroup.of (rels := relators Inc ℓ incMap) (f, ⟨c, hc0⟩) := by
  have h := theta_localEvaluation Inc ℓ incMap hc v (FreeGroup.of ⟨(f, ⟨c, hc0⟩), hf⟩)
  simpa [localEvaluation, fromLocal, includeLocal, PresentedGroup.of] using h

instance [Finite F] [NeZero ℓ] : Group.FG (N Inc ℓ incMap) := by
  exact Group.fg_of_surjective (PresentedGroup.mk_surjective (relators Inc ℓ incMap))

def EmbeddingClaim (hc : CoversPoints Inc ℓ incMap) : Prop :=
  ∀ v : V, Function.Injective (theta Inc ℓ incMap hc v)

end KaplanskyCounterexample.GluedGroup

end

end OAI
