import Mathlib
import OAI.Topology.ArtinGroups.Quivers.TraceLinear

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I J I' J' : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V] [Fintype I] [Fintype J] [Fintype I'] [Fintype J']

structure HomOperator (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (E' : BasedComplex Q (K := K) I')
    (F' : BasedComplex Q (K := K) J') where
  component : ℤ → Matrix I J (Q.Zigzag K) →ₗ[K] Matrix I' J' (Q.Zigzag K)
  preserves : ∀ n v f, f ∈ homSpace Q E F n v → component n f ∈ homSpace Q E' F' n v
  commute : ∀ n v f, f ∈ homSpace Q E F n v →
    homDifferential Q E' F' n (component n f) =
      component (n + 1) (homDifferential Q E F n f)

namespace HomOperator
variable {Q} {E : BasedComplex Q (K := K) I} {F : BasedComplex Q (K := K) J}
  {E' : BasedComplex Q (K := K) I'} {F' : BasedComplex Q (K := K) J'}

lemma map_cycles (T : HomOperator Q E F E' F') (n v : ℤ)
    {f : Matrix I J (Q.Zigzag K)} (hf : f ∈ homCycles Q E F n v) :
    T.component n f ∈ homCycles Q E' F' n v := by
  constructor
  · exact T.preserves n v f hf.1
  · change homDifferential Q E' F' n (T.component n f) = 0
    rw [T.commute n v f hf.1, show homDifferential Q E F n f = 0 from hf.2, map_zero]

lemma map_boundaries (T : HomOperator Q E F E' F') (n v : ℤ)
    {f : Matrix I J (Q.Zigzag K)} (hf : f ∈ homBoundaries Q E F n v) :
    T.component n f ∈ homBoundaries Q E' F' n v := by
  obtain ⟨g, hg, rfl⟩ := hf
  refine ⟨T.component (n - 1) g, T.preserves (n - 1) v g hg, ?_⟩
  simpa only [sub_add_cancel] using T.commute (n - 1) v g hg

noncomputable def onCycles (T : HomOperator Q E F E' F') (n v : ℤ) :
    homCycles Q E F n v →ₗ[K] homCycles Q E' F' n v :=
  (T.component n).restrict (fun _ hf => T.map_cycles n v hf)

noncomputable def onCohomology (T : HomOperator Q E F E' F') (n v : ℤ) :
    homCohomology Q E F n v →ₗ[K] homCohomology Q E' F' n v :=
  Submodule.mapQ _ _ (T.onCycles n v) (by
    intro f hf
    exact T.map_boundaries n v hf)

lemma onCohomology_mk (T : HomOperator Q E F E' F') (n v : ℤ)
    (f : homCycles Q E F n v) :
    T.onCohomology n v (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (T.onCycles n v f) := rfl

lemma onCohomology_injective (T : HomOperator Q E F E' F') (n v : ℤ)
    (hr : ∀ f, f ∈ homCycles Q E F n v →
      T.component n f ∈ homBoundaries Q E' F' n v → f ∈ homBoundaries Q E F n v) :
    Function.Injective (T.onCohomology n v) := by
  apply (LinearMap.ker_eq_bot).mp
  apply le_antisymm
  · intro x hx
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    change Submodule.Quotient.mk (T.onCycles n v f) = 0 at hx
    have hb := (Submodule.Quotient.mk_eq_zero _).mp hx
    have hf := hr f f.property hb
    change Submodule.Quotient.mk f = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr hf
  · exact bot_le

end HomOperator

lemma homDifferential_sandwich {E : BasedComplex Q (K := K) I}
    {F : BasedComplex Q (K := K) J} {E' : BasedComplex Q (K := K) I'}
    {F' : BasedComplex Q (K := K) J'} (a : Map Q E' E) (b : Map Q F F')
    (n : ℤ) (f : Matrix I J (Q.Zigzag K)) :
    homDifferential Q E' F' n (a.matrix * f * b.matrix) =
      a.matrix * homDifferential Q E F n f * b.matrix := by
  change E'.differential * (a.matrix * f * b.matrix) -
    cochainSign (K := K) n • (a.matrix * f * b.matrix * F'.differential) =
    a.matrix * (E.differential * f -
      cochainSign (K := K) n • (f * F.differential)) * b.matrix
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, a.commute]
    simp only [Matrix.mul_assoc]
  · rw [Matrix.mul_assoc, Matrix.mul_assoc, ← b.commute]
    simp only [Matrix.mul_assoc]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
