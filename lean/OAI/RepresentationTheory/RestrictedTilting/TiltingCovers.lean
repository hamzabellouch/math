import OAI.RepresentationTheory.RestrictedTilting.PolynomialCovers
import OAI.RepresentationTheory.RestrictedTilting.GoodKernelExtension

namespace OAI

namespace FiberFunctorProof
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
universe u
variable (k : Type u) [Field k]

 

inductive SteinbergGenerated (p r : ℕ) : FDRep k (SL2 k) → Prop
  | low (A) (hA : IsTilting k A) (a : ℕ) (ha : a < p^r-1)
      (hw : HasWeightsBetween A.ρ (-(a : ℤ)) a) : SteinbergGenerated p r A
  | high (X) (hX : IsTilting k X) : SteinbergGenerated p r (steinberg k p r ⊗ X)
  | of_iso {A B} (hA : SteinbergGenerated p r A) (e : A ≅ B) : SteinbergGenerated p r B
  | prod {A B} (hA : SteinbergGenerated p r A) (hB : SteinbergGenerated p r B) :
      SteinbergGenerated p r (repProduct k A B)

variable [Infinite k] (p r : ℕ) [Fact p.Prime] [CharP k p]

lemma SteinbergGenerated.tilting {A : FDRep k (SL2 k)} (h : SteinbergGenerated k p r A) :
    IsTilting k A := by
  induction h with
  | low A hA a ha hw => exact hA
  | high X hX => exact (steinberg_tilting k p r).tensor k hX
  | of_iso hA e ih => exact ih.of_iso k e
  | prod hA hB ihA ihB => exact ihA.product k ihB

 
omit [Fact p.Prime] [CharP k p] in
lemma costandard_generated_cover (n : ℕ) :
    ∃ (P : FDRep k (SL2 k)) (g : P ⟶ costandard k n),
      HasGoodKernel k g ∧ SteinbergGenerated k p r P := by
  by_cases hn : n < p^r-1
  · let P := tensorPowerFrom k (costandard k 0) n
    have hP : SteinbergGenerated k p r P := .low P
      (tensorPowerFrom_tilting k (costandard_zero_tilting k) n) n hn (by
        have h := tensorPowerFrom_weights k (costandard_rational k 0) 0
          (fun m v hm hv => costandard_weight_bound k 0 m hm v hv) n
        simpa only [Nat.zero_add, Nat.cast_zero, zero_add] using h)
    let e : costandard k (0+n) ≅ costandard k n :=
      eqToIso (congrArg (costandard k) (Nat.zero_add n))
    exact ⟨P,polynomialPowerMap k 0 n ≫ e.hom,
      (polynomialPowerMap_goodKernel k 0 n).comp k (HasGoodKernel.of_isIso k e.hom),hP⟩
  · let m := p^r-1
    let t := n-m
    let P := tensorPowerFrom k (costandard k m) t
    let X := tensorPowerFrom k (costandard k 0) t
    obtain ⟨e⟩ := tensorPowerFrom_factor k m t
    have hX : IsTilting k X := tensorPowerFrom_tilting k (costandard_zero_tilting k) t
    have hP : SteinbergGenerated k p r P :=
      (SteinbergGenerated.high X hX).of_iso e.symm
    have hmt : m+t = n := Nat.add_sub_of_le (by dsimp [m]; omega)
    let e' : costandard k (m+t) ≅ costandard k n := eqToIso (congrArg (costandard k) hmt)
    exact ⟨P,polynomialPowerMap k m t ≫ e'.hom,
      (polynomialPowerMap_goodKernel k m t).comp k (HasGoodKernel.of_isIso k e'.hom),hP⟩

 

lemma good_generated_cover (hr : 1 ≤ r) {A : FDRep k (SL2 k)}
    (hA : HasGoodFiltration k A) (hR : IsRational k A.ρ) :
    ∃ (P : FDRep k (SL2 k)) (g : P ⟶ A),
      HasGoodKernel k g ∧ SteinbergGenerated k p r P := by
  induction hA with
  | zero A hz =>
    have hAZ : ∀ x : A, x = 0 := fun x =>
      congrArg (fun f => fdrepLinear k f x) (hz.eq_zero_of_src (𝟙 A))
    have : Subsingleton A := subsingleton_of_forall_eq 0 hAZ
    have hq : 1 < p^r := Nat.one_lt_pow (by omega) (Fact.out : p.Prime).one_lt
    refine ⟨A,𝟙 A,HasGoodKernel.id k A,
      .low A (IsTilting.of_subsingleton k A hR) 0 (by omega) ?_⟩
    intro m v hm hv
    exact hAZ v
  | @step A B n f g w hS hA ih =>
    have := hS.mono_f
    have hRA : IsRational k A.ρ := IsRational.of_injective k _ _ (fdrepLinear k f)
      (fdrep_injective k f) (fdrepLinear_comm k f) hR
    obtain ⟨P,a,ha,hP⟩ := ih hRA
    obtain ⟨Q,q,hq,hQ⟩ := costandard_generated_cover k p r n
    obtain ⟨s,hs⟩ := good_weyl_lift k f g w hS hR (hQ.tilting k p r) hA q
    exact ⟨repProduct k P Q,extensionCoverMap k f a s,
      extensionCoverMap_goodKernel k f g w hS a q ha hq s hs,.prod hP hQ⟩

 

theorem tilting_retract_generated (hr : 1 ≤ r) (A : FDRep k (SL2 k)) (hA : IsTilting k A) :
    ∃ (P : FDRep k (SL2 k)) (g : P ⟶ A) (s : A ⟶ P),
      s ≫ g = 𝟙 A ∧ SteinbergGenerated k p r P := by
  obtain ⟨P,g,hg,hP⟩ := good_generated_cover k p r hr hA.2.1 hA.1
  obtain ⟨s,hs⟩ := hg.split k (hP.tilting k p r).1 hA
  exact ⟨P,g,s,hs,hP⟩
end FiberFunctorProof

end OAI
