import Mathlib
import OAI.RingTheory.Multiplicity.FrobeniusTensorTransfer

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal Topology
open Filter CategoryTheory
namespace Lech.FrobeniusIntermediate
universe u
variable {D : Type u} [CommRing D] [IsDomain D] [IsNoetherianRing D] [IsLocalRing D]
  (p : ℕ) [Fact p.Prime] [CharP D p]
  (B : Subring D) [IsLocalRing B] [IsNoetherianRing B] [IsLocalHom B.subtype]
  [Module.Finite B D]

def frobeniusModule_order_iso (e : ℕ) (he : ∀ x : D, x^(p^e) ∈ B)
    (M : ModuleCat.{u} D) (n : ℕ) :
    (ModuleCat.extendScalars B.subtype).obj
      (Lech.FrobeniusModule B p n ((ModuleCat.extendScalars (powerMap p B e he)).obj M)) ≅
      Lech.FrobeniusModule D p (e+n) M := by
  let f := powerMap p B e he
  let g := iterateFrobenius B p n
  have hx : B.subtype.comp (g.comp f) = iterateFrobenius D p (e+n) := by
    ext x
    change (x^(p^e))^(p^n) = x^(p^(e+n))
    rw [← pow_mul,← pow_add]
  let u := (ModuleCat.extendScalars B.subtype).mapIso
    ((ModuleCat.extendScalarsComp f g).app M).symm
  let v := ((ModuleCat.extendScalarsComp (g.comp f) B.subtype).app M).symm
  have q := u ≪≫ v
  rw [hx] at q
  exact q

 

omit [IsNoetherianRing D] in
theorem exists_positive_module_rank_transfer [IsNoetherianRing D] :
    ∃ r : ℕ, 0 < r ∧ ∀ (e : ℕ) (he : ∀ x : D, x^(p^e) ∈ B)
      (_hres : Function.Surjective (algebraMap (IsLocalRing.ResidueField B) (IsLocalRing.ResidueField D)))
      (M : ModuleCat.{u} D), IsFiniteLength D M → ∀ a : ℝ≥0∞,
      Tendsto (fun n => ((p : ℝ≥0∞)^(n*Lech.dimension B))⁻¹ *
        (Module.length B (Lech.FrobeniusModule B p n
          ((ModuleCat.extendScalars (powerMap p B e he)).obj M))).toENNReal)
        atTop (𝓝 a) →
      Tendsto (fun n => ((p : ℝ≥0∞)^(n*Lech.dimension B))⁻¹ *
        (Module.length D (Lech.FrobeniusModule D p n M)).toENNReal)
        atTop (𝓝 (((p : ℝ≥0∞)^(e*Lech.dimension B))⁻¹ * ((r : ℝ≥0∞)*a))) := by
  obtain ⟨r,hr,h⟩ := Lech.exists_frobenius_tensor_transfer B D p (by
    intro g hg hz
    have hc := LinearMap.congr_fun hz (1 : D)
    change (g : D) * 1 = 0 at hc
    simp only [mul_one] at hc
    exact hg (Subtype.val_injective hc))
  refine ⟨r,hr,?_⟩
  intro e he hres M hM a ha
  let N := (ModuleCat.extendScalars (powerMap p B e he)).obj M
  have := (isFiniteLength_iff_isNoetherian_isArtinian.mp hM).1
  obtain ⟨I,hI,hIM⟩ := Lech.finiteLength_primary_annihilator hM
  have hN : IsFiniteLength B N :=
    Lech.finiteLength_extendScalars_of_primary (powerMap p B e he) M I hIM
      (map_radical_primary p B e he I hI)
  have ht := h N hN a ha
  have ht' : Tendsto (fun n => ((p : ℝ≥0∞)^(n*Lech.dimension B))⁻¹ *
      (Module.length D (Lech.FrobeniusModule D p (e+n) M)).toENNReal)
      atTop (𝓝 ((r : ℝ≥0∞)*a)) := by
    apply ht.congr
    intro n
    congr 1
    rw [Lech.RootTower.length_eq_of_residue_surjective hres]
    exact congrArg ENat.toENNReal
      (frobeniusModule_order_iso p B e he M n).toLinearEquiv.length_eq
  have hp0 : (p : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hwfin : ((p : ℝ≥0∞)^(e*Lech.dimension B))⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.mpr (pow_ne_zero _ hp0)
  have ht'' := ENNReal.Tendsto.const_mul (a := ((p : ℝ≥0∞)^(e*Lech.dimension B))⁻¹)
    ht' (Or.inr hwfin)
  apply (tendsto_add_atTop_iff_nat e).mp
  apply ht''.congr
  intro n
  rw [Nat.add_comm n e,Nat.add_mul,pow_add,
    ENNReal.mul_inv (Or.inl (pow_ne_zero _ hp0)) (Or.inl (by simp)),mul_assoc]
end Lech.FrobeniusIntermediate

end

end OAI
