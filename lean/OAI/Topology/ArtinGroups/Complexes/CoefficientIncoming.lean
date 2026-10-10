import Mathlib
import OAI.Topology.ArtinGroups.Complexes.CoefficientTopDual

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]

def coefficientIncoming (E : BasedComplex Q (K := K) I) (α : V) (c : ℤ) :
    Submodule K (I → K) :=
  Submodule.span K (Set.range (fun ia : I × A => fun j => (E.differential ia.1 j).arrow ia.2) ∪
    {v | ∃ i, ((E.placement i).color ≠ α ∨ (E.placement i).cochain ≠ c) ∧ v = Pi.single i 1})

abbrev CoefficientTop (E : BasedComplex Q (K := K) I) (α : V) (c : ℤ) :=
  (I → K) ⧸ coefficientIncoming Q E α c

omit [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A] in
lemma coefficientPairing_apply (x y : I → K) :
    (Pi.basisFun K I).toDualEquiv x y = ∑ i, y i * x i := by
  rw [Module.Basis.toDualEquiv_apply]
  calc
    _ = (Pi.basisFun K I).toDual x (∑ i, ((Pi.basisFun K I).repr y) i • (Pi.basisFun K I) i) :=
      congrArg ((Pi.basisFun K I).toDual x) ((Pi.basisFun K I).sum_repr y).symm
    _ = _ := by simp only [map_sum, map_smul, smul_eq_mul,
      Module.Basis.toDual_apply_left, Pi.basisFun_repr]

omit [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A] in
lemma coefficientPairing_single (x : I → K) (i : I) :
    (Pi.basisFun K I).toDualEquiv x (Pi.single i 1) = x i := by
  rw [coefficientPairing_apply]
  simp [Pi.single_apply]

omit [Fintype V] [DecidableEq A] in
lemma coefficientTopDual_eq_annihilator (E : BasedComplex Q (K := K) I) (α : V) (c : ℤ) :
    coefficientTopDual Q E α c =
      (coefficientIncoming Q E α c).dualAnnihilator.comap
        (Pi.basisFun K I).toDualEquiv.toLinearMap := by
  ext x
  simp only [Submodule.mem_comap, LinearEquiv.coe_coe, Submodule.mem_dualAnnihilator]
  constructor
  · rintro ⟨hx,hxd⟩
    have hle : coefficientIncoming Q E α c ≤
        LinearMap.ker ((Pi.basisFun K I).toDualEquiv x) := by
      apply Submodule.span_le.mpr
      rintro v (⟨⟨i,a⟩,rfl⟩ | ⟨i,hi,rfl⟩)
      · exact (coefficientPairing_apply (fun j => x j) (fun j => (E.differential i j).arrow a)).trans
          (hxd i a)
      · change (Pi.basisFun K I).toDualEquiv x (Pi.single i 1) = 0
        simpa only [coefficientPairing_single] using hx i hi
    intro v hv
    exact hle hv
  · intro hx
    constructor
    · intro i hi
      have h := hx (Pi.single i 1) (Submodule.subset_span (Or.inr ⟨i,hi,rfl⟩))
      simpa only [coefficientPairing_single] using h
    · intro i a
      exact (coefficientPairing_apply x (fun j => (E.differential i j).arrow a)).symm.trans
        (hx _ (Submodule.subset_span (Or.inl ⟨(i,a),rfl⟩)))

noncomputable def coefficientTopEquivDual (E : BasedComplex Q (K := K) I) (α : V) (c : ℤ) :
    CoefficientTop Q E α c ≃ₗ[K] coefficientTopDual Q E α c :=
  (Subspace.quotEquivAnnihilator (coefficientIncoming Q E α c)).trans
    ((LinearEquiv.ofSubmodule' (Pi.basisFun K I).toDualEquiv
      (coefficientIncoming Q E α c).dualAnnihilator).symm.trans
        (LinearEquiv.ofEq _ _ (coefficientTopDual_eq_annihilator Q E α c).symm))

omit [Fintype V] [DecidableEq A] in
lemma coefficientTop_nontrivial_iff (E : BasedComplex Q (K := K) I) (α : V) (c : ℤ) :
    Nontrivial (CoefficientTop Q E α c) ↔ coefficientTopDual Q E α c ≠ ⊥ := by
  rw [← Submodule.nontrivial_iff_ne_bot]
  exact (coefficientTopEquivDual Q E α c).toEquiv.nontrivial_congr

omit [DecidableEq A] in
lemma pure_quotientTop_socle_totalHomDimension_pos (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) {l k : ℤ}
    (hE : ∀ i, (E.placement i).level = l) (hF : ∀ j, (F.placement j).level = k)
    (α : V) (c d : ℤ) [Nontrivial (CoefficientTop Q E α c)]
    (hs : coefficientSocle Q F α d ≠ ⊥) :
    0 < totalHomDimension Q E F (k-l) :=
  pure_top_socle_totalHomDimension_pos Q E F hE hF α c d
    ((coefficientTop_nontrivial_iff Q E α c).mp inferInstance) hs

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
