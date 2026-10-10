import Mathlib
import OAI.RingTheory.Multiplicity.ComplexTheorem

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex Lech.ProductSourceCover
open scoped ENNReal
namespace Lech
universe u
 

theorem complex_estimate_allModule (d : ℕ) (hd : 0<d) :
    ∃ A : ℝ,0≤A ∧ ∀ {C : Type u} [CommRing C] [Nontrivial C]
      (z : Fin d → C) (ell : AllModuleLength C) (e : ℝ) (_he : 0≤e)
      (_hmu : ell.value (ModuleCat.of C (C ⧸ Ideal.span (Set.range z))) = ENNReal.ofReal e)
      (_ha : ∀ a : ℕ,0<a → ell.value (ModuleCat.of C
        (C ⧸ Ideal.span (Set.range (fun j => z j^a)))) = (a:ℝ≥0∞)^d*ENNReal.ofReal e)
      (_hK : ∀ a : ℕ,1≤a → ∀ i : ℤ,i < 0 →
        ell.value ((Koszul.unit (List.ofFn (fun j => z j^a))).homology i)=0)
      (F : CochainComplex (ModuleCat.{u} C) ℤ)
      (_hf : ∀ i,Module.Free C (F.X i)) (_hfin : ∀ i,Module.Finite C (F.X i))
      (_hb : ∀ i,i < -(d:ℤ) ∨ 0 < i → IsZero (F.X i))
      (_hac : ∀ j,(((baseChangeFunctor C (Localization.Away (z j))).mapHomologicalComplex _).obj F).Acyclic)
      (s : ℕ) (_hs : 0<s)
      (_hδ : ∀ i : ℤ,(F.d i (i+1)).hom.range ≤
        (Ideal.span (Set.range z))^s • (⊤ : Submodule C (F.X (i+1))))
      (_halt : ∑ i∈Finset.range (d+1),(-1:ℝ)^i*(Module.finrank C (F.X (-(i:ℤ))):ℝ)=0),
      e*(s:ℝ)^d*((Module.finrank C (F.X 0):ℝ)-A/s*
        ∑ i∈Finset.range (d+1),(Module.finrank C (F.X (-(i:ℤ))):ℝ)) ≤
          (ell.value (F.homology 0)).toReal := by
  classical
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
  let : LinearOrder (Chart n) := LinearOrder.lift' (Fintype.equivFin (Chart n))
    (Fintype.equivFin (Chart n)).injective
  obtain ⟨A,hA,H⟩ := complex_estimate_basis n
  refine ⟨A,hA,?_⟩
  intro C _ _ z ell e he hmu ha hK F hf hfin hb hac s hs hδ halt
  let I := Ideal.span (Set.range z)
  let l := ell.torsionLength I
  let b : ℤ → ℕ := fun i => Module.finrank C (F.X i)
  let B : ∀ i,Module.Basis (Fin (b i)) C (F.X i) := fun i => by
    letI := hf i
    letI := hfin i
    exact Module.finBasis C (F.X i)
  have hds : l.DirectSumZero := fun M _ _ _ _ hh => ell.directSum_zero M hh
  have hlmu : l.value (ModuleCat.of C (C ⧸ I)) ≠ ⊤ := by
    change ell.value _ ≠ ⊤
    rw [hmu]
    exact ENNReal.ofReal_ne_top
  have hla (a : ℕ) (ha0 : 0<a) : l.value (ModuleCat.of C
      (C ⧸ Ideal.span (Set.range (fun j => z j^a)))) =
        a^(n+1) • l.value (ModuleCat.of C (C ⧸ I)) := by
    change ell.value _ = a^(n+1) • ell.value _
    rw [ha a ha0,hmu]
    simp only [nsmul_eq_mul,Nat.cast_pow]
  have H' := (H I z rfl l hds hlmu hla hK F b B (by
    simpa only [Nat.cast_add,Nat.cast_one,Nat.cast_succ] using hb) hac).2.2 s hs hδ halt
  change (ell.value (ModuleCat.of C (C ⧸ I))).toReal * _ * _ ≤ _ at H'
  rw [hmu,ENNReal.toReal_ofReal he] at H'
  exact H'
end Lech

end

end OAI
