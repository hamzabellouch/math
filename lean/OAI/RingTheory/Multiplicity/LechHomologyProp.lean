import Mathlib
import OAI.RingTheory.Multiplicity.SignedCechBicRow

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
open CategoryTheory CategoryTheory.Limits CochainComplex
open scoped ModuleCat.Algebra
open CategoryTheory CategoryTheory.Limits CochainComplex CochainComplex.HomComplex
open CochainComplex CochainComplex.HomComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators
namespace Lech
universe u
variable {R : Type u} [CommRing R] [Nontrivial R]

 

lemma homology_prop_of_koszul (P : ObjectProperty (ModuleCat.{u} R)) [P.IsSerreClass]
    (zs : List R) (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (hf : ∀ j, Module.Free R (F.X j)) (hfin : ∀ j, Module.Finite R (F.X j))
    (hb : ∀ j, j < -(zs.length : ℤ) ∨ 0 < j → IsZero (F.X j))
    (hz : ∀ a ∈ zs, Nonempty (Homotopy (a • 𝟙 F) 0))
    (hK : ∀ i, P ((Koszul.unit zs).homology i)) (i : ℤ) : P (F.homology i) := by
  have ht : P ((Koszul.tensor zs F).homology (i - zs.length)) := by
    rw [← Koszul.tensorFunctor_obj]
    apply FiniteComplex.homology_devissage P (Koszul.tensorFunctor zs)
      (Koszul.tensorSplitting zs) (-(zs.length : ℤ)) (zs.length + 1) F
      (i - zs.length) (fun j hj => hb j (by omega))
    intro j
    have := hf j
    have := hfin j
    rw [Koszul.tensorFunctor_obj]
    exact prop_tensor_free_single P zs (F.X j) j (i - zs.length) (hK _)
  simpa using Koszul.prop_homology_of_tensor P zs F hz (i - zs.length) ht

omit [Nontrivial R] in
 

lemma powerTorsion_of_le_radical {I J : Ideal R} (hI : I.FG) (hIJ : I ≤ J.radical)
    {M : ModuleCat.{u} R} (hM : powerTorsion J M) : powerTorsion I M := by
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hIJ hI
  obtain ⟨m, hm⟩ := hM
  exact ⟨n * m, by rw [pow_mul]; exact (pow_le_pow_left' hn m).trans hm⟩

 

theorem acyclicity_length (I : Ideal R) (ℓ : TorsionLength I)
    (zs : List R) (hI : I.FG) (hIJ : I ≤ (Koszul.entryIdeal zs).radical)
    (hquot : ℓ.value (ModuleCat.of R (R ⧸ Koszul.entryIdeal zs)) ≠ ⊤)
    (hK : ∀ i < 0, ℓ.value ((Koszul.unit zs).homology i) = 0)
    (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (hf : ∀ j, Module.Free R (F.X j)) (hfin : ∀ j, Module.Finite R (F.X j))
    (hb : ∀ j, j < -(zs.length : ℤ) ∨ 0 < j → IsZero (F.X j))
    (hz : ∀ a ∈ zs, Nonempty (Homotopy (a • 𝟙 F) 0)) :
    (∀ i, powerTorsion I (F.homology i) ∧ ℓ.value (F.homology i) ≠ ⊤) ∧
      (∀ i < 0, ℓ.value (F.homology i) = 0) := by
  have htors (i : ℤ) : powerTorsion I ((Koszul.unit zs).homology i) :=
    powerTorsion_of_le_radical hI hIJ (Koszul.tensor_homology_torsion zs _ i)
  have hzero (i : ℤ) (hi : i < 0) : ℓ.zeroClass ((Koszul.unit zs).homology i) :=
    ⟨htors i, hK i hi⟩
  have hquotT : powerTorsion I (ModuleCat.of R (R ⧸ Koszul.entryIdeal zs)) := by
    apply powerTorsion_of_le_radical hI hIJ
    exact ⟨1, by simp only [pow_one, Ideal.annihilator_quotient, le_refl]⟩
  have hfinite (i : ℤ) : ℓ.finiteClass ((Koszul.unit zs).homology i) := by
    rcases lt_trichotomy i 0 with hi | rfl | hi
    · exact ⟨htors i, by rw [hK i hi]; exact ENNReal.zero_ne_top⟩
    · exact ℓ.finiteClass.prop_of_epi (Koszul.unitHomologyQuotient zs) ⟨hquotT, hquot⟩
    · exact ℓ.finiteClass.prop_of_isZero (Koszul.unit_homology_zero zs i (Or.inr hi))
  exact ⟨homology_prop_of_koszul ℓ.finiteClass zs F hf hfin hb hz hfinite,
    fun i hi => (acyclicity_of_koszul ℓ.zeroClass zs F hf hfin hb hz hzero i hi).2⟩

end Lech


namespace Lech.SourceGraded
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] [Nontrivial R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : Ideal.span (Set.range z)=I)
  (ell : AllModuleLength R) (F : CochainComplex (ModuleCat.{u} R) ℤ)

include hz in
 
theorem acyclicity_finite
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
  have hq : (ell.torsionLength I).value (ModuleCat.of R
      (R ⧸ Koszul.entryIdeal (List.ofFn (fun j => z j^a))))≠⊤ := by
    change ell.value _ ≠ ⊤
    rw [entryIdeal_ofFn,ha a ha0,nsmul_eq_mul]
    exact ENNReal.mul_ne_top (by simp) hmu
  have HK : ∀ i : ℤ, i<0 → (ell.torsionLength I).value
      ((Koszul.unit (List.ofFn (fun j => z j^a))).homology i)=0 :=
    hK a (by omega)
  have H := acyclicity_length I (ell.torsionLength I) (List.ofFn (fun j => z j^a))
    hfg hrad hq HK F hf hfin (by simpa only [List.length_ofFn] using hb) (by
      intro x hx
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hx
      exact ⟨Koszul.scalarPowerHomotopy F (z j) m a (by dsimp [a];omega) (hm j).some⟩)
  refine ⟨H.1, fun i hi => ?_⟩
  rcases lt_or_gt_of_ne hi with hlt|hgt
  · exact H.2 i hlt
  · exact ell.zero (ExactAt.of_isZero (hb i (Or.inr hgt))).isZero_homology

 

theorem cech_homology_finite
    (hh : 0<h) (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
    (ha : ∀ a : ℕ, 0<a → ell.value (ModuleCat.of R
      (R ⧸ Ideal.span (Set.range (fun j => z j^a))))=a^h • ell.value (ModuleCat.of R (R ⧸ I)))
    (hK : ∀ a : ℕ, 1≤a → ∀ i : ℤ, i<0 →
      ell.value ((Koszul.unit (List.ofFn (fun j => z j^a))).homology i)=0)
    (hf : ∀ j, Module.Free R (F.X j)) (hfin : ∀ j, Module.Finite R (F.X j))
    (hb : ∀ j, j < -(h:ℤ) ∨ 0<j → IsZero (F.X j))
    (hacyc : ∀ j, ((baseChangeFunctor R (Localization.Away (z j))).mapHomologicalComplex _ |>.obj F).Acyclic) :
    (∀ i, powerTorsion I (((TensorTotal.Right.functor F).obj
        (FilteredCech.positive I z (coordinate_mem I z hz) 0)).homology i) ∧
      ell.value (((TensorTotal.Right.functor F).obj
        (FilteredCech.positive I z (coordinate_mem I z hz) 0)).homology i)≠⊤) ∧
    (∀ i : ℤ, i≠1 → ell.value (((TensorTotal.Right.functor F).obj
        (FilteredCech.positive I z (coordinate_mem I z hz) 0)).homology i)=0) := by
  have H := acyclicity_finite I z hz ell F hmu ha hK hf hfin hb hacyc
  have hc (i : ℤ) : ell.value (F.homology (i-1))=ell.value (((TensorTotal.Right.functor F).obj
      (FilteredCech.positive I z (coordinate_mem I z hz) 0)).homology i) := by
    simpa only [sub_add_cancel] using cech_homology_value I z hz ell F hh hmu ha hK hf hfin
      (-(h:ℤ)) (h+1) (by intro j hj; apply hb;omega) hacyc (i-1)
  have hp : ∀ j, Module.Projective R (F.X j) := fun j => by have := hf j; infer_instance
  refine ⟨fun i => ⟨?_,?_⟩,fun i hi => ?_⟩
  · exact FilteredCech.positive_homology_powerTorsion I z (coordinate_mem I z hz) F
      (-(h:ℤ)) 0 hp hfin hb hacyc 0 i
  · rw [←hc i]; exact (H.1 (i-1)).2
  · rw [←hc i]; exact H.2 (i-1) (by omega)

 

theorem cech_euler
    (hh : 0<h) (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
    (ha : ∀ a : ℕ, 0<a → ell.value (ModuleCat.of R
      (R ⧸ Ideal.span (Set.range (fun j => z j^a))))=a^h • ell.value (ModuleCat.of R (R ⧸ I)))
    (hK : ∀ a : ℕ, 1≤a → ∀ i : ℤ, i<0 →
      ell.value ((Koszul.unit (List.ofFn (fun j => z j^a))).homology i)=0)
    (hf : ∀ j, Module.Free R (F.X j)) (hfin : ∀ j, Module.Finite R (F.X j))
    (hb : ∀ j, j < -(h:ℤ) ∨ 0<j → IsZero (F.X j))
    (hacyc : ∀ j, ((baseChangeFunctor R (Localization.Away (z j))).mapHomologicalComplex _ |>.obj F).Acyclic) :
    ∑ j ∈ Finset.range (h+1), (-1:ℝ)^j *
      (ell.value (((TensorTotal.Right.functor F).obj
        (FilteredCech.positive I z (coordinate_mem I z hz) 0)).homology (1-(j:ℤ)))).toReal =
      (ell.value (F.homology 0)).toReal := by
  have H := cech_homology_finite I z hz ell F hh hmu ha hK hf hfin hb hacyc
  rw [Finset.sum_eq_single 0]
  · simp only [pow_zero,Nat.cast_zero,sub_zero,one_mul]
    have hc := cech_homology_value I z hz ell F hh hmu ha hK hf hfin
      (-(h:ℤ)) (h+1) (by intro j hj;apply hb;omega) hacyc 0
    simpa using congrArg ENNReal.toReal hc.symm
  · intro j _ hj
    rw [H.2 (1-(j:ℤ)) (by omega),ENNReal.toReal_zero,mul_zero]
  · simp
end Lech.SourceGraded
end

end OAI
