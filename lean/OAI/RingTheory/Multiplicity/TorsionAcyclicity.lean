import Mathlib
import OAI.RingTheory.Multiplicity.LechHomologyProp

namespace OAI

noncomputable section
namespace Lech.SourceGraded
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] [Nontrivial R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : Ideal.span (Set.range z)=I)
  (ell : TorsionLength I) (F : CochainComplex (ModuleCat.{u} R) ℤ)
include hz in
 

theorem acyclicity_finite_torsion
    (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
    (ha : ∀ a : ℕ, 0<a → ell.value (ModuleCat.of R
      (R ⧸ Ideal.span (Set.range (fun j => z j^a))))=a^h • ell.value (ModuleCat.of R (R ⧸ I)))
    (hK : ∀ a : ℕ, 1≤a → ∀ i : ℤ, i<0 →
      ell.value ((Koszul.unit (List.ofFn (fun j => z j^a))).homology i)=0)
    (hf : ∀ j, Module.Free R (F.X j)) (hfin : ∀ j, Module.Finite R (F.X j))
    (hb : ∀ j, j < -(h:ℤ) ∨ 0<j → IsZero (F.X j))
    (hacyc : ∀ j, ((baseChangeFunctor R (Localization.Away (z j))).mapHomologicalComplex _ |>.obj F).Acyclic) :
    (∀ i, powerTorsion I (F.homology i) ∧ ell.value (F.homology i)≠⊤) ∧
      (∀ i : ℤ, i≠0 → ell.value (F.homology i)=0) := by
  classical
  have hp : ∀ j, Module.Projective R (F.X j) := fun j => by have := hf j; infer_instance
  obtain ⟨m,hm⟩ := uniform_nullhomotopy_of_projective_acyclic_away z F (-(h:ℤ)) 0 hp hfin hb hacyc
  let a := m+1
  have ha0 : 0<a := by dsimp [a]; omega
  have hfg : I.FG := by
    rw [←hz]
    exact ⟨Finset.univ.image z, by simp⟩
  have hrad : I ≤ (Koszul.entryIdeal (List.ofFn (fun j => z j^a))).radical := by
    rw [←hz,entryIdeal_ofFn]
    apply Ideal.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact ⟨a,Ideal.subset_span ⟨j,rfl⟩⟩
  have hq : ell.value (ModuleCat.of R
      (R ⧸ Koszul.entryIdeal (List.ofFn (fun j => z j^a))))≠⊤ := by
    rw [entryIdeal_ofFn,ha a ha0,nsmul_eq_mul]
    exact ENNReal.mul_ne_top (by simp) hmu
  have HK : ∀ i : ℤ, i<0 → ell.value
      ((Koszul.unit (List.ofFn (fun j => z j^a))).homology i)=0 :=
    hK a (by omega)
  have H := acyclicity_length I ell (List.ofFn (fun j => z j^a))
    hfg hrad hq HK F hf hfin (by simpa only [List.length_ofFn] using hb) (by
      intro x hx
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hx
      exact ⟨Koszul.scalarPowerHomotopy F (z j) m a (by dsimp [a];omega) (hm j).some⟩)
  refine ⟨H.1, fun i hi => ?_⟩
  rcases lt_or_gt_of_ne hi with hlt|hgt
  · exact H.2 i hlt
  · exact ell.zero (ExactAt.of_isZero (hb i (Or.inr hgt))).isZero_homology

end Lech.SourceGraded

end

end OAI
