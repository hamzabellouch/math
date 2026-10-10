import Mathlib
import OAI.RingTheory.Multiplicity.ElementaryContractibleProjector
import OAI.RingTheory.Multiplicity.FiniteFreeRetract
import OAI.RingTheory.Multiplicity.NonminimalPivot

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace Lech
universe u
variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

def complexRankSum (F : CochainComplex (ModuleCat.{u} R) ℤ) : ℕ :=
  ∑ j ∈ Finset.range (dimension R+1),Module.finrank R (F.X (-(j:ℤ)))

def IsMinimalComplex (F : CochainComplex (ModuleCat.{u} R) ℤ) : Prop :=
  ∀ i : ℤ,(F.d i (i+1)).hom.range ≤ IsLocalRing.maximalIdeal R • (⊤ : Submodule R (F.X (i+1)))

omit [IsNoetherianRing R] in
lemma nonminimal_complex_reduction (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (hF : IsFiniteHomologyComplex R F) (hn : ¬ IsMinimalComplex F) :
    ∃ G : CochainComplex (ModuleCat.{u} R) ℤ,
      IsFiniteHomologyComplex R G ∧ Nonempty (HomotopyEquiv F G) ∧
        complexRankSum G < complexRankSum F := by
  classical
  obtain ⟨j,hj⟩ := not_forall.mp hn
  let := hF.term_free (j+1)
  let := hF.term_finite (j+1)
  obtain ⟨t,ht,htne⟩ := exists_nonzero_reverse_projector (F.d j (j+1)) hj
  let q := elementaryProjector F j t
  have hq : q ≫ q = q := elementaryProjector_idempotent F j t ht
  have hqn : q.f j ≠ 0 := by simpa only [q,elementaryProjector_f_left] using htne
  obtain ⟨G,K,i,r,a,b,hir,hab,hba,hs,hib,har,⟨e⟩⟩ :=
    null_projector_contractible_splitting F q hq (elementaryProjectorNull F j t)
  have hg (s : ℤ) : Module.Free R (G.X s) ∧ Module.Finite R (G.X s) := by
    let := hF.term_free s
    let := hF.term_finite s
    exact finite_free_retract (i.f s) (r.f s) (congrArg (fun u => u.f s) hir)
  have hk (s : ℤ) : Module.Free R (K.X s) ∧ Module.Finite R (K.X s) := by
    let := hF.term_free s
    let := hF.term_finite s
    exact finite_free_retract (a.f s) (b.f s) (congrArg (fun u => u.f s) hab)
  have hrank (s : ℤ) : Module.finrank R (F.X s) =
      Module.finrank R (G.X s) + Module.finrank R (K.X s) := by
    let := (hg s).1
    let := (hg s).2
    let := (hk s).1
    let := (hk s).2
    let ee := complementaryRetractEquiv (i.f s) (r.f s) (a.f s) (b.f s)
      (congrArg (fun u => u.f s) hir) (congrArg (fun u => u.f s) hab)
      (congrArg (fun u => u.f s) hs) (congrArg (fun u => u.f s) hib)
      (congrArg (fun u => u.f s) har)
    rw [ee.finrank_eq,Module.finrank_prod]
  have hG : IsFiniteHomologyComplex R G :=
    { term_free := fun s => (hg s).1
      term_finite := fun s => (hg s).2
      bounded := fun s hs => isZero_of_retract (i.f s) (r.f s)
        (congrArg (fun u => u.f s) hir) (hF.bounded s hs)
      homology_finite_length := fun s => by
        apply Module.length_ne_top_iff.mp
        rw [← (e.toHomologyIso s).toLinearEquiv.length_eq]
        exact Module.length_ne_top_iff.mpr (hF.homology_finite_length s) }
  have hKne : ¬ IsZero (K.X j) := by
    intro hz
    apply hqn
    rw [← hba]
    change b.f j ≫ a.f j = 0
    rw [hz.eq_of_tgt (b.f j) 0,zero_comp]
  have hpos : 0 < Module.finrank R (K.X j) := by
    let := (hk j).1
    let := (hk j).2
    apply (Module.finrank_pos_iff_of_free R (K.X j)).mpr
    exact not_subsingleton_iff_nontrivial.mp
      (fun hh => hKne (ModuleCat.isZero_iff_subsingleton.mpr hh))
  have hjbounds : -(dimension R:ℤ) ≤ j ∧ j ≤ 0 := by
    constructor
    · by_contra! h
      exact hqn ((hF.bounded j (Or.inl h)).eq_of_src _ _)
    · by_contra! h
      exact hqn ((hF.bounded j (Or.inr h)).eq_of_src _ _)
  have hjnat : -(((-j).toNat:ℕ):ℤ) = j := by omega
  refine ⟨G,hG,⟨e⟩,?_⟩
  apply Finset.sum_lt_sum
  · intro s _
    rw [hrank]
    omega
  · refine ⟨(-j).toNat,Finset.mem_range.mpr (by omega),?_⟩
    change Module.finrank R (G.X (-(((-j).toNat:ℕ):ℤ))) <
      Module.finrank R (F.X (-(((-j).toNat:ℕ):ℤ)))
    rw [hjnat,hrank]
    omega
end Lech

end

end OAI
