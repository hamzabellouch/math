import Mathlib
import OAI.Topology.ArtinGroups.Complexes.SecondaryLayer

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V]
variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def supportedCoefficientCycles (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hE : E.IsMinimal Q) (hF : F.IsMinimal Q)
    (U : Set V) (q d n v : ℤ) :
    Submodule K (Matrix {i // (E.placement i).level = q}
      {j // (F.placement j).level = d} (Q.Zigzag K)) where
  carrier := {f | f ∈ homCycles Q (E.pureLayer Q hE q) (F.pureLayer Q hF d) n v ∧
    CoefficientMatrix Q f ∧ ∀ i j, (E.placement i.val).color ∉ U → f i j = 0}
  zero_mem' := ⟨Submodule.zero_mem _, fun _ _ => ⟨rfl, rfl⟩, fun _ _ _ => rfl⟩
  add_mem' := by
    intro f g hf hg
    refine ⟨Submodule.add_mem _ hf.1 hg.1, ?_, ?_⟩
    · intro i j
      constructor
      · change (f i j).arrow + (g i j).arrow = 0
        rw [(hf.2.1 i j).1, (hg.2.1 i j).1, add_zero]
      · change (f i j).token + (g i j).token = 0
        rw [(hf.2.1 i j).2, (hg.2.1 i j).2, add_zero]
    · intro i j h
      change f i j + g i j = 0
      rw [hf.2.2 i j h, hg.2.2 i j h, add_zero]
  smul_mem' := by
    intro r f hf
    refine ⟨Submodule.smul_mem _ r hf.1, ?_, ?_⟩
    · intro i j
      constructor
      · change r • (f i j).arrow = 0
        rw [(hf.2.1 i j).1, smul_zero]
      · change r • (f i j).token = 0
        rw [(hf.2.1 i j).2, smul_zero]
    · intro i j h
      change r • f i j = 0
      rw [hf.2.2 i j h, smul_zero]

noncomputable def secondaryOnCycles (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hE : E.IsMinimal Q) (hF : F.IsMinimal Q)
    (U : Set V) (q d n v : ℤ) :
    supportedCoefficientCycles Q E F hE hF U q d n v →ₗ[K]
      homCycles Q (E.pureLayer Q hE q) (F.pureLayer Q hF (d-1)) (n+1) v :=
  (secondaryLayer Q E F q d n).restrict fun _ hf =>
    secondaryLayer_mem_cycles Q E F hE hF q d n v hf.1

noncomputable def secondaryOnCohomology (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hE : E.IsMinimal Q) (hF : F.IsMinimal Q)
    (U : Set V) (q d n v : ℤ) :
    supportedCoefficientCycles Q E F hE hF U q d n v →ₗ[K]
      homCohomology Q (E.pureLayer Q hE q) (F.pureLayer Q hF (d-1)) (n+1) v :=
  ((homBoundaries Q (E.pureLayer Q hE q) (F.pureLayer Q hF (d-1)) (n+1) v).comap
    (homCycles Q (E.pureLayer Q hE q) (F.pureLayer Q hF (d-1)) (n+1) v).subtype).mkQ.comp
    (secondaryOnCycles Q E F hE hF U q d n v)

lemma secondaryOnCohomology_injective [Fintype V]
    (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    (hE : E.IsMinimal Q) (hF : F.IsMinimal Q) (U : Set V) (q d n v : ℤ)
    (hcap : E.CappedOn Q U q) (hd : homDimension Q E F n v = 0) :
    Function.Injective (secondaryOnCohomology Q E F hE hF U q d n v) := by
  apply (LinearMap.ker_eq_bot).mp
  apply le_antisymm _ bot_le
  intro f hf
  change Submodule.Quotient.mk (secondaryOnCycles Q E F hE hF U q d n v f) = 0 at hf
  have hb := (Submodule.Quotient.mk_eq_zero _).mp hf
  change f = 0
  apply Subtype.ext
  exact capped_secondary_kernel_zero Q E F hE hF U q d n v hcap hd
    f.property.1 f.property.2.1 f.property.2.2 hb

lemma supportedCoefficient_finrank_le [Fintype V] [DecidableEq A]
    (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    (hE : E.IsMinimal Q) (hF : F.IsMinimal Q) (U : Set V) (q d n v : ℤ)
    (hcap : E.CappedOn Q U q) (hd : homDimension Q E F n v = 0) :
    Module.finrank K (supportedCoefficientCycles Q E F hE hF U q d n v) ≤
      homDimension Q (E.pureLayer Q hE q) (F.pureLayer Q hF (d-1)) (n+1) v :=
  LinearMap.finrank_le_finrank_of_injective
    (secondaryOnCohomology_injective Q E F hE hF U q d n v hcap hd)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
