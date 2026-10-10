import OAI.RingTheory.Tachikawa.StableLift

namespace OAI


noncomputable section
namespace Tachikawa.SourceField
abbrev Base := MvPolynomial (Fin 3) (ZMod 2)
abbrev K := FractionRing Base

def parameter (i : Fin 3) : K := algebraMap Base K (MvPolynomial.X i)
def q : K := parameter 0
def H₁ : K := parameter 1
def H₂ : K := parameter 2

lemma parameter_ne_zero (i : Fin 3) : parameter i ≠ 0 := by
  intro h
  apply MvPolynomial.X_ne_zero (R := ZMod 2) (s := i)
  apply IsFractionRing.injective Base K
  exact h.trans (map_zero _).symm

lemma one_add_q_pow_ne_zero (n : ℕ) (hn : 0 < n) : 1 + q^n ≠ 0 := by
  intro h
  have he : 1 + (MvPolynomial.X (0 : Fin 3) : Base)^n = 0 := by
    apply IsFractionRing.injective Base K
    simpa only [map_add, map_one, map_pow, map_zero, q, parameter] using h
  have hv := congrArg (MvPolynomial.eval (fun _ : Fin 3 => (0 : ZMod 2))) he
  have hv' : (1 : ZMod 2) = 0 := by
    simpa only [map_add, map_one, map_pow, map_zero, MvPolynomial.eval_X,
      zero_pow (Nat.ne_of_gt hn), add_zero] using hv
  exact one_ne_zero hv'

lemma distinct_parameter_powers {i j : Fin 3} (hij : i ≠ j) (n : ℕ) (hn : 0 < n) :
    parameter i ^ n ≠ parameter j ^ n := by
  intro h
  have he : (MvPolynomial.X i : Base)^n = (MvPolynomial.X j)^n := by
    apply IsFractionRing.injective Base K
    simpa only [parameter, map_pow] using h
  let v : Fin 3 → ZMod 2 := fun t => if t = i then 0 else 1
  have hv := congrArg (MvPolynomial.eval v) he
  have hji : j ≠ i := Ne.symm hij
  simp [v, hji, Nat.ne_of_gt hn] at hv

lemma H_powers_distinct (n : ℕ) (hn : 0 < n) : H₁^n ≠ H₂^n :=
  distinct_parameter_powers (by decide) n hn

lemma H_inverse_powers_distinct (n : ℕ) (hn : 0 < n) : (H₁^n)⁻¹ ≠ (H₂^n)⁻¹ := by
  intro h
  exact H_powers_distinct n hn (inv_injective h)

end Tachikawa.SourceField



namespace Tachikawa.MissingYProfile
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2]

def finiteYX (q : k) : FiniteModule k (Construction.E q) where
  obj := Enveloping.evalObj (Construction.xObj q) (Construction.Y q).obj
  finite := inferInstance

def shift (q : k) (M : FiniteModule k (Construction.E q)) : ℤ → FiniteModule k (Construction.E q)
  | .ofNat n => M.negative (Construction.formE q) n
  | .negSucc n => M.positive (n+1)

abbrev W (q : k) (a : ℤ) := StableHom (k := k) (R := Construction.E q)
  (M := Construction.xObj q) (N := (shift q (finiteYX q) a).obj)

def profile (q : k) : Prop := ∀ a : ℤ,
  ((a = -3 ∨ a = 0) → Nonempty (W q a ≃ₗ[k] k)) ∧
  (a ≠ -3 → a ≠ 0 → Subsingleton (W q a))

def sourceProfile : Prop := profile SourceField.q

theorem W_zero_nontrivial (q H : k) (hq : q ≠ 0) (hH : H ≠ 0) : Nontrivial (W q 0) := by
  obtain ⟨g,hg⟩ := Construction.exists_nonzero_X_YX q H hH hq
  let f := ((Construction.uXIso q H hH).inv ≫ Enveloping.evalMap (Construction.xObj q) g).hom
  refine ⟨⟨Submodule.Quotient.mk f, 0, ?_⟩⟩
  intro h
  exact hg ((Submodule.Quotient.mk_eq_zero _).mp h)

theorem source_W_zero_nontrivial : Nontrivial (W SourceField.q 0) :=
  W_zero_nontrivial SourceField.q SourceField.H₁
    (SourceField.parameter_ne_zero 0) (SourceField.parameter_ne_zero 1)

end Tachikawa.MissingYProfile



namespace Tachikawa.Construction
open CategoryTheory HomologicalComplex
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)
variable (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)

abbrev evalK := ((Enveloping.evaluation (k := k) (xObj q)).mapHomologicalComplex _).obj
  (Enveloping.inducedRegularComplex (inclusionB q))

omit [CharP k 2] in
lemma evalK_finite (n : ℕ) : Module.Finite (E q) ((evalK q).X n) := by
  change Module.Finite (E q) (Enveloping.evalObj (xObj q)
    ((Enveloping.inducedRegularComplex (inclusionB q)).X n))
  infer_instance

omit [CharP k 2] in
lemma evalK_projective (n : ℕ) : Module.Projective (E q) ((evalK q).X n) := by
  change Module.Projective (E q) (Enveloping.evalObj (xObj q)
    ((Enveloping.inducedRegularComplex (inclusionB q)).X n))
  infer_instance

lemma natJJ_finite (n : ℕ) : Module.Finite (E q) ((natJJ q hp).X n) := by
  let := forwardJJ_finite q hp (n:ℤ)
  exact Module.Finite.equiv (jjNatIntIso q hp n).toLinearEquiv.symm

lemma natJJ_projective (n : ℕ) : Module.Projective (E q) ((natJJ q hp).X n) := by
  let := forwardJJ_projective q hp (n:ℤ)
  exact Module.Projective.of_equiv (jjNatIntIso q hp n).toLinearEquiv.symm

def evalFiveFiberStableEquiv : StableEquiv (k := k)
    (Enveloping.evalObj (xObj q) (Enveloping.inducedCokerFive (inclusionB q)).obj)
    (ModuleCat.of (E q) (CokerAt (jjFiber q hq hp) 5)) := by
  let := evalK_finite q 4
  let := evalK_projective q 4
  let := natJJ_finite q hp 4
  let := natJJ_projective q hp 4
  let e : HomotopyEquiv (evalK q) (natJJ q hp) := evaluatedKJComparison q hp
  let e₁ := Enveloping.evalCokerIso (xObj q)
    ((Enveloping.inducedRegularComplex (inclusionB q)).d 6 5)
  exact (StableEquiv.ofLinearEquiv e₁.toLinearEquiv).trans
    ((NatCoker.stableEquiv e 4).trans
      (StableEquiv.ofLinearEquiv (natJJFiveFiberEquiv q hq hp)))

end Tachikawa.Construction



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [Module.Injective R R]
variable {M N P Q M' N' : ModuleCat.{0} R}
variable [Module.Finite R P] [Module.Projective R P]
  [Module.Finite R Q] [Module.Projective R Q]

omit [Module.Injective R R] [Module.Finite R P] [Module.Projective R P]
  [Module.Finite R Q] [Module.Projective R Q] in
lemma exact_square_difference_inverse
    (i : M →ₗ[R] P) (pi : P →ₗ[R] M')
    (j : N →ₗ[R] Q) (delta : Q →ₗ[R] N')
    (f : M →ₗ[R] N) (h : P →ₗ[R] Q) (g : M' →ₗ[R] N')
    (f' : N →ₗ[R] M) (h' : Q →ₗ[R] P) (g' : N' →ₗ[R] M')
    (hu : h.comp i = j.comp f) (hl : delta.comp h = g.comp pi)
    (hu' : h'.comp j = i.comp f') (hl' : pi.comp h' = g'.comp delta) :
    (h'.comp h - LinearMap.id).comp i = i.comp (f'.comp f - LinearMap.id) ∧
    pi.comp (h'.comp h - LinearMap.id) = (g'.comp g - LinearMap.id).comp pi := by
  constructor
  · simp only [LinearMap.sub_comp, LinearMap.comp_sub, LinearMap.id_comp,
      LinearMap.comp_id, LinearMap.comp_assoc]
    rw [hu, ← LinearMap.comp_assoc, hu', LinearMap.comp_assoc]
  · simp only [LinearMap.sub_comp, LinearMap.comp_sub, LinearMap.id_comp,
      LinearMap.comp_id]
    rw [← LinearMap.comp_assoc, hl', LinearMap.comp_assoc, hl, ← LinearMap.comp_assoc]

def StableEquiv.ofExactSquares
    (i : M →ₗ[R] P) (pi : P →ₗ[R] M') (hi : Function.Injective i)
    (hex : Function.Exact i pi) (hpi : Function.Surjective pi)
    (j : N →ₗ[R] Q) (delta : Q →ₗ[R] N') (hj : Function.Injective j)
    (hex' : Function.Exact j delta) (hdelta : Function.Surjective delta)
    (e : StableEquiv (k := k) M N)
    (h : P →ₗ[R] Q) (g : M' →ₗ[R] N')
    (h' : Q →ₗ[R] P) (g' : N' →ₗ[R] M')
    (hu : h.comp i = j.comp e.hom) (hl : delta.comp h = g.comp pi)
    (hu' : h'.comp j = i.comp e.inv) (hl' : pi.comp h' = g'.comp delta) :
    StableEquiv (k := k) M' N' where
  hom := g
  inv := g'
  inv_hom := by
    obtain ⟨a,b⟩ := exact_square_difference_inverse i pi j delta e.hom h g e.inv h' g'
      hu hl hu' hl'
    exact (exact_square_factors_iff i pi hi hex hpi i pi hi hex hpi
      _ _ _ a b).mp e.inv_hom
  hom_inv := by
    obtain ⟨a,b⟩ := exact_square_difference_inverse j delta i pi e.inv h' g' e.hom h g
      hu' hl' hu hl
    exact (exact_square_factors_iff j delta hj hex' hdelta j delta hj hex' hdelta
      _ _ _ a b).mp e.hom_inv

def StableEquiv.down
    (i : M →ₗ[R] P) (pi : P →ₗ[R] M') (hi : Function.Injective i)
    (hex : Function.Exact i pi) (hpi : Function.Surjective pi)
    (j : N →ₗ[R] Q) (delta : Q →ₗ[R] N') (hj : Function.Injective j)
    (hex' : Function.Exact j delta) (hdelta : Function.Surjective delta)
    (e : StableEquiv (k := k) M N) : StableEquiv (k := k) M' N' := by
  have H := exists_exact_square_down i pi hi hex hpi j delta hex' e.hom
  have H' := exists_exact_square_down j delta hj hex' hdelta i pi hex e.inv
  exact e.ofExactSquares i pi hi hex hpi j delta hj hex' hdelta
    H.choose H.choose_spec.choose H'.choose H'.choose_spec.choose
    H.choose_spec.choose_spec.1 H.choose_spec.choose_spec.2
    H'.choose_spec.choose_spec.1 H'.choose_spec.choose_spec.2

omit [Module.Injective R R] [Module.Finite R P] [Module.Finite R Q]
  [Module.Projective R Q] in

theorem exists_exact_square_up
    (i : M →ₗ[R] P) (pi : P →ₗ[R] M') (hex : Function.Exact i pi)
    (j : N →ₗ[R] Q) (delta : Q →ₗ[R] N') (hj : Function.Injective j)
    (hex' : Function.Exact j delta) (hdelta : Function.Surjective delta)
    (g : M' →ₗ[R] N') :
    ∃ (h : P →ₗ[R] Q) (f : M →ₗ[R] N),
      h.comp i = j.comp f ∧ delta.comp h = g.comp pi := by
  obtain ⟨h,hh⟩ := Module.projective_lifting_property delta (g.comp pi) hdelta
  have hr (x : M) : (h.comp i) x ∈ LinearMap.range j := by
    apply (hex' _).mp
    have he := LinearMap.congr_fun hh (i x)
    change delta (h (i x)) = g (pi (i x)) at he
    change delta (h (i x)) = 0
    rw [he, (hex _).mpr ⟨x,rfl⟩, map_zero]
  let f := CokerAt.factorThrough j hj (h.comp i) hr
  exact ⟨h,f,(CokerAt.factorThrough_spec j hj (h.comp i) hr).symm,hh⟩

def StableEquiv.up
    (i : M →ₗ[R] P) (pi : P →ₗ[R] M') (hi : Function.Injective i)
    (hex : Function.Exact i pi) (hpi : Function.Surjective pi)
    (j : N →ₗ[R] Q) (delta : Q →ₗ[R] N') (hj : Function.Injective j)
    (hex' : Function.Exact j delta) (hdelta : Function.Surjective delta)
    (e : StableEquiv (k := k) M' N') : StableEquiv (k := k) M N := by
  have H := exists_exact_square_up i pi hex j delta hj hex' hdelta e.hom
  have H' := exists_exact_square_up j delta hex' i pi hi hex hpi e.inv
  let h := H.choose
  let f := H.choose_spec.choose
  let h' := H'.choose
  let f' := H'.choose_spec.choose
  have hu : h.comp i = j.comp f := H.choose_spec.choose_spec.1
  have hl : delta.comp h = e.hom.comp pi := H.choose_spec.choose_spec.2
  have hu' : h'.comp j = i.comp f' := H'.choose_spec.choose_spec.1
  have hl' : pi.comp h' = e.inv.comp delta := H'.choose_spec.choose_spec.2
  refine ⟨f,f',?_,?_⟩
  · obtain ⟨a,b⟩ := exact_square_difference_inverse i pi j delta f h e.hom f' h' e.inv
      hu hl hu' hl'
    exact (exact_square_factors_iff i pi hi hex hpi i pi hi hex hpi
      _ _ _ a b).mpr e.inv_hom
  · obtain ⟨a,b⟩ := exact_square_difference_inverse j delta i pi f' h' e.inv f h e.hom
      hu' hl' hu hl
    exact (exact_square_factors_iff j delta hj hex' hdelta j delta hj hex' hdelta
      _ _ _ a b).mpr e.hom_inv
end Tachikawa



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  [FiniteDimensional k R] [FiniteDimensional k S]
  (t : SymmetrizingForm (k := k) (R := R)) (u : SymmetrizingForm (k := k) (R := S))
  (X : ModuleCat.{0} R) [FiniteDimensional k X]
  (M : FiniteModule k (Alg k S R)) [Module.Projective Rᵐᵒᵖ (Obj M.obj)]
  (P : ChainComplex (ModuleCat.{0} S) ℤ) (hP : ComplexExact P)
  (fin : ∀ j, Module.Finite S (P.X j)) (proj : ∀ j, Module.Projective S (P.X j))

omit [Module.Projective Rᵐᵒᵖ (Obj M.obj)] in
lemma evalFree_finite (Q : ModuleCat.{0} (Alg k S R)) [Module.Finite (Alg k S R) Q] :
    Module.Finite S (evalObj (k := k) X Q) := by
  let : FiniteDimensional k Q := Module.Finite.trans (Alg k S R) Q
  infer_instance

def evalCosyCokerStableEquiv (j : ℤ)
    (e : StableEquiv (k := k) (evalObj (k := k) X M.obj) (ModuleCat.of S (CokerAt P j))) :
    StableEquiv (k := k) (evalObj (k := k) X (M.cosyzygy (envelopingForm u t)).obj)
      (ModuleCat.of S (CokerAt P (j-1))) := by
  let τ := envelopingForm u t
  let J := ModuleCat.of (Alg k S R) (Fin (Module.finrank k M) → Alg k S R)
  let : Module.Finite (Alg k S R) J := inferInstanceAs (Module.Finite (Alg k S R) (Fin (Module.finrank k M) → Alg k S R))
  let : Module.Projective (Alg k S R) J := inferInstanceAs (Module.Projective (Alg k S R) (Fin (Module.finrank k M) → Alg k S R))
  let : Module.Finite S (evalObj (k := k) X J) := evalFree_finite (k := k) X J
  let : Module.Projective S (evalObj (k := k) X J) := by infer_instance
  let i : M.obj ⟶ J := ModuleCat.ofHom (M.embed τ)
  let p : J ⟶ (M.cosyzygy τ).obj := ModuleCat.ofHom (LinearMap.range (M.embed τ)).mkQ
  have hi : Function.Injective i := M.embed_injective τ
  have he : Function.Exact i p := fun _ => Submodule.Quotient.mk_eq_zero _
  have hs : Function.Surjective p := Submodule.mkQ_surjective _
  let : Module.Injective S S := u.injective
  let := fin (j-1)
  let := proj (j-1)
  exact StableEquiv.down (P := evalObj (k := k) X J) (Q := P.X (j-1))
    (evalMap (k := k) X i).hom (evalMap (k := k) X p).hom
    (evalMap_injective X t i hi) (evalMap_exact X t i p hi he hs) (evalMap_surjective X p hs)
    (CokerAt.δ P j (j-1)) (CokerAt.π P (j-1))
    (CokerAt.δ_injective P hP j (j-1) (by omega))
    (CokerAt.δ_π_exact P j (j-1) (by omega)) (CokerAt.π_surjective P (j-1)) e

end Tachikawa.Enveloping



namespace Tachikawa.Construction
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)
variable (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)

def evalNegativeFiveFiberStableEquiv (n : ℕ) : StableEquiv (k := k)
    (Enveloping.evalObj (xObj q)
      ((Enveloping.inducedCokerFive (inclusionB q)).negative
        (Enveloping.envelopingForm (formE q) (formE q)) n).obj)
    (ModuleCat.of (E q) (CokerAt (jjFiber q hq hp) (5-(n:ℤ)))) := by
  let N := Enveloping.inducedCokerFive (inclusionB q)
  let τ := Enveloping.envelopingForm (formE q) (formE q)
  let := c5_left_projective q hq
  let := c5_right_projective q hq
  induction n with
  | zero => exact evalFiveFiberStableEquiv q hq hp
  | succ n ih =>
    let : Module.Projective (E q)ᵐᵒᵖ (Enveloping.Obj (N.negative τ n).obj) :=
      (Enveloping.negative_side_projective (formE q) (formE q) N n).2
    have e := Enveloping.evalCosyCokerStableEquiv (formE q) (formE q) (xObj q)
      (N.negative τ n) (jjFiber q hq hp) (jjFiber_totallyAcyclic q hq hp).1
      (jjFiber_finite q hq hp) (jjFiber_projective q hq hp) (5-(n:ℤ)) ih
    change StableEquiv (k := k) (Enveloping.evalObj (xObj q) ((N.negative τ n).cosyzygy τ).obj)
      (ModuleCat.of (E q) (CokerAt (jjFiber q hq hp) (5-((n+1:ℕ):ℤ))))
    rw [show 5-((n+1:ℕ):ℤ) = (5-(n:ℤ))-1 by omega]
    exact e

def yxFiberStableEquiv : StableEquiv (k := k) (MissingYProfile.finiteYX q).obj
    (ModuleCat.of (E q) (CokerAt (jjFiber q hq hp) 1)) :=
  evalNegativeFiveFiberStableEquiv q hq hp 4

end Tachikawa.Construction



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]
variable (t : SymmetrizingForm (k := k) (R := R))
  (P : ChainComplex (ModuleCat.{0} R) ℤ) (hP : ComplexExact P)
  (fin : ∀ j, Module.Finite R (P.X j)) (proj : ∀ j, Module.Projective R (P.X j))

def cosyCokerStableEquiv (M : FiniteModule k R) (j : ℤ)
    (e : StableEquiv (k := k) M.obj (ModuleCat.of R (CokerAt P j))) :
    StableEquiv (k := k) (M.cosyzygy t).obj (ModuleCat.of R (CokerAt P (j-1))) := by
  let : Module.Injective R R := t.injective
  let := fin (j-1)
  let := proj (j-1)
  exact StableEquiv.down (P := ModuleCat.of R (Fin (Module.finrank k M) → R))
    (Q := P.X (j-1)) (M.embed t) (M.cosyzygyProjection t) (M.embed_injective t)
    (M.cosyzygyProjection_exact t) (M.cosyzygyProjection_surjective t)
    (CokerAt.δ P j (j-1)) (CokerAt.π P (j-1))
    (CokerAt.δ_injective P hP j (j-1) (by omega))
    (CokerAt.δ_π_exact P j (j-1) (by omega)) (CokerAt.π_surjective P (j-1)) e

def syzyCokerStableEquiv (M : FiniteModule k R) (j : ℤ)
    (e : StableEquiv (k := k) M.obj (ModuleCat.of R (CokerAt P j))) :
    StableEquiv (k := k) M.syzygy.obj (ModuleCat.of R (CokerAt P (j+1))) := by
  let : Module.Injective R R := t.injective
  let := fin j
  let := proj j
  exact StableEquiv.up (P := ModuleCat.of R (Fin M.cover.rank → R))
    (Q := P.X j) M.syzygyInclusion M.cover.map M.syzygyInclusion_injective
    M.syzygyInclusion_exact M.cover.surjective
    (CokerAt.δ P (j+1) j) (CokerAt.π P j)
    (CokerAt.δ_injective P hP (j+1) j rfl)
    (CokerAt.δ_π_exact P (j+1) j rfl) (CokerAt.π_surjective P j) e

def negativeCokerStableEquiv (M : FiniteModule k R) (j : ℤ)
    (e : StableEquiv (k := k) M.obj (ModuleCat.of R (CokerAt P j))) (n : ℕ) :
    StableEquiv (k := k) (M.negative t n).obj (ModuleCat.of R (CokerAt P (j-(n:ℤ)))) := by
  induction n with
  | zero =>
    change StableEquiv (k := k) M.obj (ModuleCat.of R (CokerAt P (j-0)))
    rw [sub_zero]
    exact e
  | succ n ih =>
    change StableEquiv (k := k) ((M.negative t n).cosyzygy t).obj _
    rw [show j-((n+1:ℕ):ℤ) = (j-(n:ℤ))-1 by omega]
    exact cosyCokerStableEquiv t P hP fin proj _ _ ih

def positiveCokerStableEquiv (M : FiniteModule k R) (j : ℤ)
    (e : StableEquiv (k := k) M.obj (ModuleCat.of R (CokerAt P j))) (n : ℕ) :
    StableEquiv (k := k) (M.positive n).obj (ModuleCat.of R (CokerAt P (j+(n:ℤ)))) := by
  induction n with
  | zero =>
    change StableEquiv (k := k) M.obj (ModuleCat.of R (CokerAt P (j+0)))
    rw [add_zero]
    exact e
  | succ n ih =>
    change StableEquiv (k := k) (M.positive n).syzygy.obj _
    rw [show j+((n+1:ℕ):ℤ) = (j+(n:ℤ))+1 by omega]
    exact syzyCokerStableEquiv t P hP fin proj _ _ ih

end Tachikawa



namespace Tachikawa
variable {k R M N N' : Type} [Field k] [Ring R] [Algebra k R]
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup N']
  [Module R M] [Module R N] [Module R N']
  [Module k N] [Module k N'] [IsScalarTower k R N] [IsScalarTower k R N']

def stablePostEquiv (e : N ≃ₗ[R] N') :
    StableHom (k := k) (R := R) (M := M) (N := N) ≃ₗ[k]
      StableHom (k := k) (R := R) (M := M) (N := N') :=
  { stablePostcompose e.toLinearMap with
    invFun := stablePostcompose e.symm.toLinearMap
    left_inv := by
      intro x
      obtain ⟨f,rfl⟩ := stableClass_surjective x
      change stableClass (k := k) (e.symm.toLinearMap.comp (e.toLinearMap.comp f)) = stableClass (k := k) f
      congr 1
      ext z
      exact e.symm_apply_apply (f z)
    right_inv := by
      intro x
      obtain ⟨f,rfl⟩ := stableClass_surjective x
      change stableClass (k := k) (e.toLinearMap.comp (e.symm.toLinearMap.comp f)) = stableClass (k := k) f
      congr 1
      ext z
      exact e.apply_symm_apply (f z) }
end Tachikawa



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]
variable (t : SymmetrizingForm (k := k) (R := R))
  (P : ChainComplex (ModuleCat.{0} R) ℤ) (hP : ComplexExact P)
  (fin : ∀ j, Module.Finite R (P.X j)) (proj : ∀ j, Module.Projective R (P.X j))

def finiteCoker (j : ℤ) : FiniteModule k R where
  obj := ModuleCat.of R (CokerAt P j)
  finite := by
    let := fin j
    exact inferInstanceAs (Module.Finite R (P.X j ⧸ LinearMap.range (P.d (j+1) j).hom))

def completeCokerDuality (j : ℤ) (N : ModuleCat.{0} R) :
    StableMap (k := k) N (ModuleCat.of R (CokerAt P (j+1))) ≃ₗ[k]
      Module.Dual k (StableMap (k := k) (ModuleCat.of R (CokerAt P j)) N) := by
  let M := finiteCoker (k := k) P fin j
  let e := syzyCokerStableEquiv t P hP fin proj M j (StableEquiv.refl _)
  let e₀ := stablePostEquiv (k := k) (R := R) (M := N)
    (N := M.syzygy.obj) (N' := LinearMap.ker M.cover.map) (LinearEquiv.refl R _)
  exact (e.post N).symm.trans (e₀.trans
    (t.stableDualEquiv M.cover.map M.cover.surjective (M.embed t) (M.embed_injective t)
      M.syzygy.cover.map M.syzygy.cover.surjective))

end Tachikawa



namespace Tachikawa.C
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] (q : k)

def homCfSimpleEquiv : (Cf q →ₗ[C k q] Simple q) ≃ₗ[k] k where
  toFun f := f (LeftCorner.generator (f_idempotent q))
  invFun a := LeftCorner.lift (show Simple q from a) (f_smul_simple q a)
  left_inv _ := LeftCorner.hom_ext (f_idempotent q) (f_smul_simple q _)
  right_inv a := f_smul_simple q a
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

local instance simpleGround : Module k (simpleObj q) := ModuleCat.Algebra.instModuleCarrier

def inducedFHomEquiv : (inducedObj q 0 ⟶ simpleObj q) ≃ₗ[k] k := by
  let : Module.Finite k (Cf q) := Module.Finite.of_injective
    ((Cf q).subtype.restrictScalars k) Subtype.val_injective
  let e := (TrivialInflation.homEquiv (k := k) (R := C k q) (M := Cf q)
    (N := Simple q)).trans (homCfSimpleEquiv q)
  exact {
    toFun := fun f => e f.hom
    invFun := fun a => ModuleCat.ofHom (e.symm a)
    left_inv := fun f => ModuleCat.hom_ext (e.symm_apply_apply f.hom)
    right_inv := e.apply_symm_apply
    map_add' := fun f g => e.map_add f.hom g.hom
    map_smul' := by
      intro r f
      change Construction.characterT q (algebraMap k (T q) r) *
        (show k from f (TrivialInduction.unit (LeftCorner.generator (f_idempotent q)))) =
        r * (show k from f (TrivialInduction.unit (LeftCorner.generator (f_idempotent q))))
      rw [AlgHom.commutes]
      rfl }

variable [CharP k 2]

lemma forwardJ_hom_zero (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)
    (j : ℤ) (hj : j ≠ 0) (f : (Construction.forwardJ q hp).X j ⟶ simpleObj q) : f = 0 := by
  cases j with
  | ofNat n =>
    cases n with
    | zero => exact (hj rfl).elim
    | succ n => exact induced_positive_hom_zero q n f
  | negSucc n => exact (Construction.forwardJ_below q hp _ (by omega)).eq_of_src _ _

lemma reverseJ_hom_zero (hq : q ≠ 0) (j : ℤ) (hj : j ≠ 2)
    (f : (Construction.reverseJ q hq).X j ⟶ simpleObj q) : f = 0 := by
  cases j with
  | ofNat n =>
    rcases n with _ | _ | _ | n
    · exact induced_positive_hom_zero q 0 f
    · exact induced_positive_hom_zero q 0 f
    · exact (hj rfl).elim
    · exact (Construction.reverseJ_above q hq _ (by change 2 < ((n+3 : ℕ) : ℤ); omega)).eq_of_src _ _
  | negSucc n => exact induced_positive_hom_zero q 0 f

end Tachikawa.C



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
variable {k : Type} [Field k]

def piSupportedEquiv {ι : Type} (V : ι → Type) [∀ i, AddCommGroup (V i)]
    [∀ i, Module k (V i)] (i₀ : ι) (hz : ∀ i, i ≠ i₀ → Subsingleton (V i)) :
    (∀ i, V i) ≃ₗ[k] V i₀ := by
  classical
  apply LinearEquiv.ofBijective (LinearMap.proj i₀)
  constructor
  · intro x y h
    funext i
    by_cases hi : i = i₀
    · subst i; exact h
    · exact (hz i hi).elim _ _
  · intro x
    refine ⟨Pi.single i₀ x, ?_⟩
    exact Pi.single_eq_same i₀ x

namespace OuterTensor
variable {A B : Type} [Ring A] [Ring B] [Algebra k A] [Algebra k B]
  (P : ChainComplex (ModuleCat.{0} A) ℤ) (Q : ChainComplex (ModuleCat.{0} B) ℤ)
  (U : ModuleCat A) (V : ModuleCat B)

lemma hom_zero_left (M : ModuleCat A) (N : ModuleCat B)
    [Module.Finite A M] [Module.Finite B N] [Module.Projective A M] [Module.Projective B N]
    (hz : ∀ f : M ⟶ U, f = 0)
    (f : ((bifunctor k A B).obj M |>.obj N) ⟶ ((bifunctor k A B).obj U |>.obj V)) : f = 0 := by
  let : Subsingleton (M ⟶ U) := ⟨fun f g => (hz f).trans (hz g).symm⟩
  obtain ⟨x,rfl⟩ := homMap_surjective (k := k) M U N V f
  rw [Subsingleton.elim x 0, map_zero]

lemma hom_zero_right (M : ModuleCat A) (N : ModuleCat B)
    [Module.Finite A M] [Module.Finite B N] [Module.Projective A M] [Module.Projective B N]
    (hz : ∀ f : N ⟶ V, f = 0)
    (f : ((bifunctor k A B).obj M |>.obj N) ⟶ ((bifunctor k A B).obj U |>.obj V)) : f = 0 := by
  let : Subsingleton (N ⟶ V) := ⟨fun f g => (hz f).trans (hz g).symm⟩
  obtain ⟨x,rfl⟩ := homMap_surjective (k := k) M U N V f
  rw [Subsingleton.elim x 0, map_zero]

lemma total_hom_zero (a b n : ℤ) (hn : n ≠ a+b)
    (fP : ∀ i, Module.Finite A (P.X i)) (fQ : ∀ j, Module.Finite B (Q.X j))
    (pP : ∀ i, Module.Projective A (P.X i)) (pQ : ∀ j, Module.Projective B (Q.X j))
    (zP : ∀ i, i ≠ a → ∀ f : P.X i ⟶ U, f = 0)
    (zQ : ∀ j, j ≠ b → ∀ f : Q.X j ⟶ V, f = 0)
    (f : (mapBifunctor P Q (bifunctor k A B) (.down ℤ)).X n ⟶
      ((bifunctor k A B).obj U).obj V) : f = 0 := by
  apply HomologicalComplex₂.total.hom_ext
  intro i j hij
  let := fP i
  let := fQ j
  let := pP i
  let := pQ j
  rw [comp_zero]
  by_cases hi : i = a
  · exact hom_zero_right U V (P.X i) (Q.X j) (zQ j (by dsimp at hij; omega)) _
  · exact hom_zero_left U V (P.X i) (Q.X j) (zP i hi) _

def totalHomSupported (a b : ℤ)
    (fP : ∀ i, Module.Finite A (P.X i)) (fQ : ∀ j, Module.Finite B (Q.X j))
    (pP : ∀ i, Module.Projective A (P.X i)) (pQ : ∀ j, Module.Projective B (Q.X j))
    (zP : ∀ i, i ≠ a → ∀ f : P.X i ⟶ U, f = 0)
    (zQ : ∀ j, j ≠ b → ∀ f : Q.X j ⟶ V, f = 0) :
    ((mapBifunctor P Q (bifunctor k A B) (.down ℤ)).X (a+b) ⟶
      ((bifunctor k A B).obj U).obj V) ≃ₗ[k]
      (((bifunctor k A B).obj (P.X a)).obj (Q.X b) ⟶
      ((bifunctor k A B).obj U).obj V) := by
  let I := {ij : ℤ × ℤ // ij.1+ij.2=a+b}
  let F := fun ij : I => ((bifunctor k A B).obj (P.X ij.val.1)).obj (Q.X ij.val.2)
  let W := ((bifunctor k A B).obj U).obj V
  change (∐ F ⟶ W) ≃ₗ[k] _
  refine (coproductHomEquiv F W).trans (piSupportedEquiv _ (⟨(a,b),rfl⟩ : I) ?_)
  intro ij hij
  let := fP ij.val.1
  let := fQ ij.val.2
  let := pP ij.val.1
  let := pQ ij.val.2
  have hz (f : F ij ⟶ W) : f = 0 := by
    by_cases h : ij.val.1 = a
    · apply hom_zero_right U V (P.X ij.val.1) (Q.X ij.val.2) _ f
      apply zQ
      intro h'
      apply hij
      exact Subtype.ext (Prod.ext h h')
    · exact hom_zero_left U V (P.X ij.val.1) (Q.X ij.val.2) (zP _ h) f
  exact ⟨fun f g => (hz f).trans (hz g).symm⟩

end OuterTensor
end Tachikawa



namespace Tachikawa.Construction
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)
local instance simpleGround : Module k (C.simpleObj q) := ModuleCat.Algebra.instModuleCarrier

lemma forwardJJ_hom_zero (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)
    (j : ℤ) (hj : j ≠ 0) (f : (forwardJJ q hp).X j ⟶ XTensorObj q) : f = 0 := by
  apply OuterTensor.total_hom_zero (forwardJ q hp) (forwardJ q hp)
    (C.simpleObj q) (C.simpleObj q) 0 0 j (by simpa using hj)
    (fun i => by
      let := forwardJ_finite q hp i
      exact Module.Finite.of_restrictScalars_finite k _ _)
    (fun i => by
      let := forwardJ_finite q hp i
      exact Module.Finite.of_restrictScalars_finite k _ _)
    (forwardJ_projective q hp) (forwardJ_projective q hp)
    (C.forwardJ_hom_zero q hp) (C.forwardJ_hom_zero q hp) f

lemma reverseJJ_hom_zero (hq : q ≠ 0)
    (j : ℤ) (hj : j ≠ 4) (f : (reverseJJ q hq).X j ⟶ XTensorObj q) : f = 0 := by
  apply OuterTensor.total_hom_zero (reverseJ q hq) (reverseJ q hq)
    (C.simpleObj q) (C.simpleObj q) 2 2 j (by simpa using hj)
    (fun i => by
      let := reverseJ_finite q hq i
      exact Module.Finite.of_restrictScalars_finite k _ _)
    (fun i => by
      let := reverseJ_finite q hq i
      exact Module.Finite.of_restrictScalars_finite k _ _)
    (reverseJ_projective q hq) (reverseJ_projective q hq)
    (C.reverseJ_hom_zero q hq) (C.reverseJ_hom_zero q hq) f

def forwardJJHomEquiv (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    ((forwardJJ q hp).X 0 ⟶ XTensorObj q) ≃ₗ[k] k := by
  let f (i : ℤ) : Module.Finite (C.T q) ((forwardJ q hp).X i) := by
    let := forwardJ_finite q hp i
    exact Module.Finite.of_restrictScalars_finite k _ _
  let e := OuterTensor.totalHomSupported (k := k) (forwardJ q hp) (forwardJ q hp)
    (C.simpleObj q) (C.simpleObj q) 0 0 f f
    (forwardJ_projective q hp) (forwardJ_projective q hp)
    (C.forwardJ_hom_zero q hp) (C.forwardJ_hom_zero q hp)
  let := C.inducedObj_finite q 0
  let : Module.Finite (C.T q) (C.inducedObj q 0) := Module.Finite.of_restrictScalars_finite k _ _
  let := C.inducedObj_projective q 0
  exact e.trans ((OuterTensor.homEquiv (C.inducedObj q 0) (C.simpleObj q)
    (C.inducedObj q 0) (C.simpleObj q)).symm.trans
    ((TensorProduct.congr (C.inducedFHomEquiv q) (C.inducedFHomEquiv q)).trans
      (TensorProduct.lid k k)))

def reverseJJHomEquiv (hq : q ≠ 0) :
    ((reverseJJ q hq).X 4 ⟶ XTensorObj q) ≃ₗ[k] k := by
  let f (i : ℤ) : Module.Finite (C.T q) ((reverseJ q hq).X i) := by
    let := reverseJ_finite q hq i
    exact Module.Finite.of_restrictScalars_finite k _ _
  let e := OuterTensor.totalHomSupported (k := k) (reverseJ q hq) (reverseJ q hq)
    (C.simpleObj q) (C.simpleObj q) 2 2 f f
    (reverseJ_projective q hq) (reverseJ_projective q hq)
    (C.reverseJ_hom_zero q hq) (C.reverseJ_hom_zero q hq)
  let := C.inducedObj_finite q 0
  let : Module.Finite (C.T q) (C.inducedObj q 0) := Module.Finite.of_restrictScalars_finite k _ _
  let := C.inducedObj_projective q 0
  exact e.trans ((OuterTensor.homEquiv (C.inducedObj q 0) (C.simpleObj q)
    (C.inducedObj q 0) (C.simpleObj q)).symm.trans
    ((TensorProduct.congr (C.inducedFHomEquiv q) (C.inducedFHomEquiv q)).trans
      (TensorProduct.lid k k)))

def jjFiberHomEquiv (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) (j : ℤ) :
    ((jjFiber q hq hp).X j ⟶ XTensorObj q) ≃ₗ[k]
    (((reverseJJ q hq).X (j+1) ⟶ XTensorObj q) ×
      ((forwardJJ q hp).X j ⟶ XTensorObj q)) :=
  ModuleCat.homLinearEquiv.trans ((LinearMap.coprodEquiv k).symm.trans
    (LinearEquiv.prodCongr ModuleCat.homLinearEquiv.symm ModuleCat.homLinearEquiv.symm))

lemma jjFiber_hom_zero (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)
    (j : ℤ) (h0 : j ≠ 0) (h3 : j ≠ 3)
    (f : (jjFiber q hq hp).X j ⟶ XTensorObj q) : f = 0 := by
  apply (jjFiberHomEquiv q hq hp j).injective
  rw [map_zero]
  apply Prod.ext
  · exact reverseJJ_hom_zero q hq (j+1) (by omega) _
  · exact forwardJJ_hom_zero q hp j h0 _

def jjFiberHomZeroEquiv (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    ((jjFiber q hq hp).X 0 ⟶ XTensorObj q) ≃ₗ[k] k := by
  let : Subsingleton ((reverseJJ q hq).X (0+1) ⟶ XTensorObj q) :=
    ⟨fun f g => (reverseJJ_hom_zero q hq _ (by norm_num) f).trans
      (reverseJJ_hom_zero q hq _ (by norm_num) g).symm⟩
  let : Unique ((reverseJJ q hq).X (0+1) ⟶ XTensorObj q) := ⟨⟨0⟩, fun _ => Subsingleton.elim _ _⟩
  exact (jjFiberHomEquiv q hq hp 0).trans ((LinearEquiv.prodComm k _ _).trans
    (LinearEquiv.prodUnique.trans (forwardJJHomEquiv q hp)))

def jjFiberHomThreeEquiv (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    ((jjFiber q hq hp).X 3 ⟶ XTensorObj q) ≃ₗ[k] k := by
  let : Subsingleton ((forwardJJ q hp).X 3 ⟶ XTensorObj q) :=
    ⟨fun f g => (forwardJJ_hom_zero q hp _ (by norm_num) f).trans
      (forwardJJ_hom_zero q hp _ (by norm_num) g).symm⟩
  let : Unique ((forwardJJ q hp).X 3 ⟶ XTensorObj q) := ⟨⟨0⟩, fun _ => Subsingleton.elim _ _⟩
  exact (jjFiberHomEquiv q hq hp 3).trans
    (LinearEquiv.prodUnique.trans (reverseJJHomEquiv q hq))

end Tachikawa.Construction



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable (P : ChainComplex (ModuleCat R) ℤ) (N : ModuleCat R)

lemma stableCoker_subsingleton (j : ℤ) (hz : ∀ f : P.X j ⟶ N, f = 0) :
    Subsingleton (StableHom (k := k) (R := R) (M := CokerAt P j) (N := N)) := by
  have hzero (x : StableHom (k := k) (R := R) (M := CokerAt P j) (N := N)) : x = 0 := by
    obtain ⟨f,rfl⟩ := stableClass_surjective x
    have hf : f = 0 := by
      apply LinearMap.ext
      intro x
      obtain ⟨y,rfl⟩ := CokerAt.π_surjective P j x
      exact LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp
        (hz (ModuleCat.ofHom (f.comp (CokerAt.π P j))))) y
    rw [hf,map_zero]
  exact ⟨fun x y => (hzero x).trans (hzero y).symm⟩

def cokerHomIsolated (j : ℤ) (hz : ∀ f : P.X (j+1) ⟶ N, f = 0) :
    (P.X j ⟶ N) →ₗ[k] (CokerAt P j →ₗ[R] N) where
  toFun f := CokerAt.descend P j f.hom
    (ModuleCat.hom_ext_iff.mp (hz (P.d (j+1) j ≫ f)))
  map_add' f g := by
    apply LinearMap.ext
    intro x
    obtain ⟨y,rfl⟩ := CokerAt.π_surjective P j x
    rfl
  map_smul' r f := by
    apply LinearMap.ext
    intro x
    obtain ⟨y,rfl⟩ := CokerAt.π_surjective P j x
    rfl

def stableCokerIsolatedEquiv (hP : TotallyAcyclic P)
    (fin : ∀ j, Module.Finite R (P.X j))
    (proj : ∀ j, Module.Projective R (P.X j))
    (j : ℤ) (hnext : ∀ f : P.X (j+1) ⟶ N, f = 0)
    (hprev : ∀ f : P.X (j-1) ⟶ N, f = 0) :
    (P.X j ⟶ N) ≃ₗ[k] StableHom (k := k) (R := R) (M := CokerAt P j) (N := N) := by
  let d := cokerHomIsolated (k := k) P N j hnext
  let e := (stableClass (k := k)).comp d
  refine LinearEquiv.ofBijective e ⟨?_, ?_⟩
  · apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro f hf
    have hf' : d f ∈ projectiveFactors (k := k) := (stableClass_eq_zero_iff _).mp hf
    obtain ⟨g,hg⟩ := (hP.factors_iff_boundary (k := k) fin proj j f.hom
      (ModuleCat.hom_ext_iff.mp (hnext (P.d (j+1) j ≫ f)))).mp hf'
    have hg0 : g = 0 := ModuleCat.hom_ext_iff.mp (hprev (ModuleCat.ofHom g))
    apply ModuleCat.hom_ext
    rw [hg0, LinearMap.zero_comp] at hg
    exact hg.symm
  · intro x
    obtain ⟨f,rfl⟩ := stableClass_surjective x
    refine ⟨ModuleCat.ofHom (f.comp (CokerAt.π P j)), ?_⟩
    apply congrArg (stableClass (k := k))
    apply LinearMap.ext
    intro y
    obtain ⟨z,rfl⟩ := CokerAt.π_surjective P j y
    rfl

end Tachikawa



namespace Tachikawa.Construction
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)

theorem jjFiber_stable_zero (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)
    (j : ℤ) (h0 : j ≠ 0) (h3 : j ≠ 3) :
    Subsingleton (StableHom (k := k) (R := E q)
      (M := CokerAt (jjFiber q hq hp) j) (N := XTensorObj q)) :=
  stableCoker_subsingleton _ _ j (jjFiber_hom_zero q hq hp j h0 h3)

def jjFiberStableZeroEquiv (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    StableHom (k := k) (R := E q)
      (M := CokerAt (jjFiber q hq hp) 0) (N := XTensorObj q) ≃ₗ[k] k :=
  (stableCokerIsolatedEquiv _ _ (jjFiber_totallyAcyclic q hq hp)
    (jjFiber_finite q hq hp) (jjFiber_projective q hq hp) 0
    (jjFiber_hom_zero q hq hp _ (by norm_num) (by norm_num))
    (jjFiber_hom_zero q hq hp _ (by norm_num) (by norm_num))).symm.trans
    (jjFiberHomZeroEquiv q hq hp)

def jjFiberStableThreeEquiv (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    StableHom (k := k) (R := E q)
      (M := CokerAt (jjFiber q hq hp) 3) (N := XTensorObj q) ≃ₗ[k] k :=
  (stableCokerIsolatedEquiv _ _ (jjFiber_totallyAcyclic q hq hp)
    (jjFiber_finite q hq hp) (jjFiber_projective q hq hp) 3
    (jjFiber_hom_zero q hq hp _ (by norm_num) (by norm_num))
    (jjFiber_hom_zero q hq hp _ (by norm_num) (by norm_num))).symm.trans
    (jjFiberHomThreeEquiv q hq hp)

theorem jjFiber_stable_profile (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)
    (j : ℤ) :
    ((j = 0 ∨ j = 3) → Nonempty (StableHom (k := k) (R := E q)
      (M := CokerAt (jjFiber q hq hp) j) (N := XTensorObj q) ≃ₗ[k] k)) ∧
    (j ≠ 0 → j ≠ 3 → Subsingleton (StableHom (k := k) (R := E q)
      (M := CokerAt (jjFiber q hq hp) j) (N := XTensorObj q))) := by
  constructor
  · rintro (rfl | rfl)
    · exact ⟨jjFiberStableZeroEquiv q hq hp⟩
    · exact ⟨jjFiberStableThreeEquiv q hq hp⟩
  · exact jjFiber_stable_zero q hq hp j

end Tachikawa.Construction



namespace Tachikawa.Construction
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)
variable (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)

def yxShiftFiberStableEquiv (a : ℤ) : StableEquiv (k := k)
    (MissingYProfile.shift q (MissingYProfile.finiteYX q) a).obj
    (ModuleCat.of (E q) (CokerAt (jjFiber q hq hp) (1-a))) := by
  cases a with
  | ofNat n =>
    exact negativeCokerStableEquiv (formE q) _
      (jjFiber_totallyAcyclic q hq hp).1 (jjFiber_finite q hq hp) (jjFiber_projective q hq hp)
      _ 1 (yxFiberStableEquiv q hq hp) n
  | negSucc n =>
    change StableEquiv (k := k) ((MissingYProfile.finiteYX q).positive (n+1)).obj _
    rw [show 1-Int.negSucc n = 1+((n+1:ℕ):ℤ) by omega]
    exact positiveCokerStableEquiv (formE q) _
      (jjFiber_totallyAcyclic q hq hp).1 (jjFiber_finite q hq hp) (jjFiber_projective q hq hp)
      _ 1 (yxFiberStableEquiv q hq hp) (n+1)

def WFiberDualEquiv (a : ℤ) : MissingYProfile.W q a ≃ₗ[k]
    Module.Dual k (StableHom (k := k) (R := E q)
      (M := CokerAt (jjFiber q hq hp) (-a)) (N := XTensorObj q)) := by
  let e₁ := (yxShiftFiberStableEquiv q hq hp a).post (xObj q)
  have e₂ := completeCokerDuality (formE q) (jjFiber q hq hp)
    (jjFiber_totallyAcyclic q hq hp).1 (jjFiber_finite q hq hp) (jjFiber_projective q hq hp)
    (-a) (xObj q)
  rw [show -a+1 = 1-a by omega] at e₂
  let e₃ := (StableEquiv.ofLinearEquiv (k := k) (M := XTensorObj q) (N := xObj q)
    (XTensorEquiv q)).post (ModuleCat.of (E q) (CokerAt (jjFiber q hq hp) (-a)))
  exact e₁.trans (e₂.trans e₃.dualMap)

include hq hp in
theorem y_profile : MissingYProfile.profile q := by
  intro a
  constructor
  · intro ha
    obtain ⟨e⟩ := (jjFiber_stable_profile q hq hp (-a)).1 (by omega)
    exact ⟨(WFiberDualEquiv q hq hp a).trans
      (e.symm.dualMap.trans (LinearMap.ringLmapEquivSelf k k k))⟩
  · intro h3 h0
    let := jjFiber_stable_zero q hq hp (-a) (by omega) (by omega)
    let : Subsingleton (Module.Dual k (StableHom (k := k) (R := E q)
        (M := CokerAt (jjFiber q hq hp) (-a)) (N := XTensorObj q))) := by
      constructor
      intro f g
      ext x
      have hx : x = 0 := Subsingleton.elim _ _
      rw [hx,map_zero,map_zero]
    exact (WFiberDualEquiv q hq hp a).injective.subsingleton

theorem source_y_profile : MissingYProfile.sourceProfile :=
  y_profile SourceField.q (SourceField.parameter_ne_zero 0) SourceField.one_add_q_pow_ne_zero

end Tachikawa.Construction



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable (P : ChainComplex (ModuleCat R) ℤ) (hP : ComplexExact P)

def cokerKernelEquiv (i : ℤ) : CokerAt P (i+1) ≃ₗ[R] LinearMap.ker (CokerAt.π P i) := by
  let f := (CokerAt.δ P (i+1) i).codRestrict (LinearMap.ker (CokerAt.π P i))
    (fun x => (CokerAt.δ_π_exact P (i+1) i rfl _).mpr ⟨x,rfl⟩)
  apply LinearEquiv.ofBijective f
  constructor
  · intro x y h
    exact CokerAt.δ_injective P hP (i+1) i rfl (congrArg Subtype.val h)
  · intro y
    obtain ⟨x,hx⟩ := (CokerAt.δ_π_exact P (i+1) i rfl y).mp y.property
    exact ⟨x,Subtype.ext hx⟩

variable (Q : ChainComplex (ModuleCat R) ℤ) (hQ : ComplexExact Q)
  (fP : ∀ i, Module.Finite R (P.X i)) (pP : ∀ i, Module.Projective R (P.X i))
  (fQ : ∀ i, Module.Finite R (Q.X i)) (pQ : ∀ i, Module.Projective R (Q.X i))
  [Module.Injective R R]

def cokerStableHomSucc (i j : ℤ) :
    StableMap (k := k) (ModuleCat.of R (CokerAt P i)) (ModuleCat.of R (CokerAt Q j)) ≃ₗ[k]
    StableMap (k := k) (ModuleCat.of R (CokerAt P (i+1))) (ModuleCat.of R (CokerAt Q (j+1))) := by
  let := fP i
  let := pP i
  let := fQ j
  let := pQ j
  let e := StableShift.equiv (k := k) (CokerAt.π P i) (CokerAt.π Q j)
    (CokerAt.π_surjective Q j) (CokerAt.π_surjective P i)
  let eP := StableEquiv.ofLinearEquiv (k := k)
    (M := ModuleCat.of R (CokerAt P (i+1)))
    (N := ModuleCat.of R (LinearMap.ker (CokerAt.π P i))) (cokerKernelEquiv P hP i)
  let eQ := StableEquiv.ofLinearEquiv (k := k)
    (M := ModuleCat.of R (CokerAt Q (j+1)))
    (N := ModuleCat.of R (LinearMap.ker (CokerAt.π Q j))) (cokerKernelEquiv Q hQ j)
  exact e.trans ((eP.pre _).symm.trans (eQ.post _).symm)

def cokerStableHomNat (i j : ℤ) (n : ℕ) :
    StableMap (k := k) (ModuleCat.of R (CokerAt P i)) (ModuleCat.of R (CokerAt Q j)) ≃ₗ[k]
    StableMap (k := k) (ModuleCat.of R (CokerAt P (i+(n:ℤ)))) (ModuleCat.of R (CokerAt Q (j+(n:ℤ)))) := by
  induction n with
  | zero =>
    rw [Nat.cast_zero,add_zero,add_zero]
  | succ n ih =>
    have e := cokerStableHomSucc P hP Q hQ fP pP fQ pQ (i+(n:ℤ)) (j+(n:ℤ)) (k := k)
    rw [show i+((n+1:ℕ):ℤ) = i+(n:ℤ)+1 by omega,
      show j+((n+1:ℕ):ℤ) = j+(n:ℤ)+1 by omega]
    exact ih.trans e

def cokerStableHomTranslate (i j a : ℤ) :
    StableMap (k := k) (ModuleCat.of R (CokerAt P i)) (ModuleCat.of R (CokerAt Q j)) ≃ₗ[k]
    StableMap (k := k) (ModuleCat.of R (CokerAt P (i+a))) (ModuleCat.of R (CokerAt Q (j+a))) := by
  cases a with
  | ofNat n => exact cokerStableHomNat P hP Q hQ fP pP fQ pQ i j n
  | negSucc n =>
    have e := (cokerStableHomNat P hP Q hQ fP pP fQ pQ
      (i+Int.negSucc n) (j+Int.negSucc n) (n+1) (k := k)).symm
    rw [show i+Int.negSucc n+((n+1:ℕ):ℤ)=i by omega,
      show j+Int.negSucc n+((n+1:ℕ):ℤ)=j by omega] at e
    exact e

end Tachikawa



namespace Tachikawa.Construction
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)
  (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)

def finiteX : FiniteModule k (E q) where
  obj := xObj q
  finite := Module.Finite.of_restrictScalars_finite k _ _

abbrev xComplete := (finiteX q).complete (formE q)

def completeYStableEquiv (a : ℤ) :
    StableMap (k := k) (ModuleCat.of (E q) (CokerAt (xComplete q) a))
      (MissingYProfile.finiteYX q).obj ≃ₗ[k] MissingYProfile.W q a := by
  let : Module.Injective (E q) (E q) := (formE q).injective
  let e₁ := (yxFiberStableEquiv q hq hp).post
    (ModuleCat.of (E q) (CokerAt (xComplete q) a))
  have e₂ := cokerStableHomTranslate (xComplete q) ((finiteX q).complete_exact (formE q))
    (jjFiber q hq hp) (jjFiber_totallyAcyclic q hq hp).1
    ((finiteX q).complete_finite (formE q)) ((finiteX q).complete_projective (formE q))
    (jjFiber_finite q hq hp) (jjFiber_projective q hq hp) 0 (1-a) a (k := k)
  rw [zero_add,show 1-a+a=1 by omega] at e₂
  let e₃ := (StableEquiv.ofLinearEquiv (k := k)
    (M := ModuleCat.of (E q) (CokerAt (xComplete q) 0)) (N := xObj q)
    ((finiteX q).cokerEquiv (formE q))).pre
      (ModuleCat.of (E q) (CokerAt (jjFiber q hq hp) (1-a)))
  let e₄ := (yxShiftFiberStableEquiv q hq hp a).post (xObj q)
  exact e₁.trans (e₂.symm.trans (e₃.trans e₄.symm))

def completeYHomologyEquiv (a : ℤ) :
    VectorSplit.H (completeHom (k := k) (xComplete q) (MissingYProfile.finiteYX q).obj) a ≃ₗ[k]
      MissingYProfile.W q a :=
  (CompleteHom.equiv (xComplete q) (MissingYProfile.finiteYX q).obj
    ((finiteX q).complete_totallyAcyclic (formE q))
    ((finiteX q).complete_finite (formE q)) ((finiteX q).complete_projective (formE q)) a).trans
      (completeYStableEquiv q hq hp a)

include hq hp in
lemma completeYHomology_zero (a : ℤ) (h3 : a ≠ -3) (h0 : a ≠ 0) :
    Subsingleton (VectorSplit.H
      (completeHom (k := k) (xComplete q) (MissingYProfile.finiteYX q).obj) a) := by
  let := (y_profile q hq hp a).2 h3 h0
  exact (completeYHomologyEquiv q hq hp a).injective.subsingleton

end Tachikawa.Construction



namespace Tachikawa.CompleteHom
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
  (P : ChainComplex (ModuleCat.{0} R) ℤ)
  (hP : TotallyAcyclic P) (fin : ∀ j, Module.Finite R (P.X j))
  (proj : ∀ j, Module.Projective R (P.X j))

lemma equiv_quotient (N : ModuleCat.{0} R) (a : ℤ)
    (z : VectorSplit.Z (completeHom (k := k) P N) a) :
    equiv P N hP fin proj a (VectorSplit.quotient _ a z) =
      stableClass (k := k) ((cokerCycles P N a).symm z) := rfl

lemma equiv_natural {M N : ModuleCat.{0} R} (f : M ⟶ N) (a : ℤ)
    (x : VectorSplit.H (completeHom (k := k) P M) a) :
    equiv P N hP fin proj a (completeHmap P f a x) =
      stablePostcompose f.hom (equiv P M hP fin proj a x) := by
  obtain ⟨z,rfl⟩ := VectorSplit.quotient_surjective a x
  change stableClass (k := k) _ = stableClass (k := k) _
  congr 1
  apply LinearMap.ext
  intro x
  obtain ⟨y,rfl⟩ := CokerAt.π_surjective P a x
  rfl

variable {X : ModuleCat.{0} R} (e : CokerAt P 0 ≃ₗ[R] X)

def zeroEquiv (N : ModuleCat.{0} R) :
    VectorSplit.H (completeHom (k := k) P N) 0 ≃ₗ[k] StableMap (k := k) X N :=
  (equiv P N hP fin proj 0).trans ((StableEquiv.ofLinearEquiv (k := k)
    (M := ModuleCat.of R (CokerAt P 0)) (N := X) e).pre N)

lemma zeroEquiv_natural {M N : ModuleCat.{0} R} (f : M ⟶ N)
    (x : VectorSplit.H (completeHom (k := k) P M) 0) :
    zeroEquiv P hP fin proj e N (completeHmap P f 0 x) =
      stablePostcompose f.hom (zeroEquiv P hP fin proj e M x) := by
  obtain ⟨z,rfl⟩ := VectorSplit.quotient_surjective 0 x
  change stableClass (k := k) _ = stableClass (k := k) _
  congr 1
  apply LinearMap.ext
  intro x
  obtain ⟨y,hy⟩ := CokerAt.π_surjective P 0 (e.symm x)
  change ((cokerCycles P N 0).symm
    (VectorSplit.cycleMap (completeHomMap P f) 0 z)) (e.symm x) =
    f (((cokerCycles P M 0).symm z) (e.symm x))
  rw [← hy]
  rfl

end Tachikawa.CompleteHom

namespace Tachikawa
variable {k V W : Type*} [Field k] [AddCommGroup V] [AddCommGroup W]
  [Module k V] [Module k W]
lemma linear_surjective_to_line (f : V →ₗ[k] W) (e : W ≃ₗ[k] k)
    (x : V) (hx : f x ≠ 0) : Function.Surjective f := by
  have hn : e (f x) ≠ 0 := fun h => hx (e.injective (h.trans (map_zero e).symm))
  intro y
  refine ⟨(e y / e (f x)) • x,?_⟩
  apply e.injective
  rw [map_smul,map_smul,smul_eq_mul,div_mul_cancel₀ _ hn]
end Tachikawa



namespace Tachikawa
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable (C : ChainComplex (ModuleCat R) ℤ) (hC : TotallyAcyclic C)
  (fin : ∀ j, Module.Finite R (C.X j)) (proj : ∀ j, Module.Projective R (C.X j))
  (N : ModuleCat R)

namespace CompleteStableExt
abbrev Q := completeResolutionTail C hC.1 proj

def cycles (n : ℕ) :
    (CokerAt C (n : ℤ) →ₗ[R] N) →ₗ[k]
      VectorSplit.Z (resolutionHom k R (Q C hC proj).complex N) n where
  toFun f := ⟨ModuleCat.ofHom (f.comp (CokerAt.π C (n : ℤ))), by
    erw [resolutionHom_memZ,completeResolutionTail_d]
    apply ModuleCat.hom_ext
    change (f.comp (CokerAt.π C (n : ℤ))).comp
      (C.d ((n+1 : ℕ) : ℤ) (n : ℤ)).hom = 0
    rw [LinearMap.comp_assoc, Nat.cast_add, Nat.cast_one, CokerAt.π_d,
      LinearMap.comp_zero]⟩
  map_add' f g := by rfl
  map_smul' c f := by rfl

def toExt (n : ℕ) : (CokerAt C (n : ℤ) →ₗ[R] N) →ₗ[k]
    Ext (ModuleCat.of R (CokerAt C 0)) N n :=
  (resolutionCyclesToExt N (Q C hC proj) n).comp (cycles C hC proj N n)

lemma toExt_surjective (n : ℕ) : Function.Surjective (toExt C hC proj N n (k := k)) := by
  intro x
  obtain ⟨f,hf,rfl⟩ := (Q C hC proj).extMk_surjective x (n+1) rfl
  rw [completeResolutionTail_d] at hf
  have hf' : f.hom.comp (C.d ((n : ℤ)+1) (n : ℤ)).hom = 0 := by
    have h := congrArg ModuleCat.Hom.hom hf
    change f.hom.comp (C.d ((n+1 : ℕ) : ℤ) (n : ℤ)).hom = 0 at h
    rw [show ((n+1 : ℕ) : ℤ) = (n : ℤ)+1 by omega] at h
    exact h
  use CokerAt.descend C (n : ℤ) f.hom hf'
  rfl

include fin in
lemma toExt_kernel (n : ℕ) :
    LinearMap.ker (toExt C hC proj N (n+1) (k := k)) =
      projectiveFactors (k := k) (M := CokerAt C ((n+1 : ℕ) : ℤ)) (N := N) := by
  ext f
  have hz : (f.comp (CokerAt.π C ((n+1 : ℕ) : ℤ))).comp
      (C.d (((n+1 : ℕ) : ℤ)+1) ((n+1 : ℕ) : ℤ)).hom = 0 := by
    rw [LinearMap.comp_assoc,CokerAt.π_d,LinearMap.comp_zero]
  have hdesc : CokerAt.descend C ((n+1 : ℕ) : ℤ)
      (f.comp (CokerAt.π C ((n+1 : ℕ) : ℤ))) hz = f := by
    apply LinearMap.ext
    intro x
    obtain ⟨y,rfl⟩ := CokerAt.π_surjective C ((n+1 : ℕ) : ℤ) x
    rfl
  have hf : (Q C hC proj).complex.d (n+2) (n+1) ≫
      ModuleCat.ofHom (f.comp (CokerAt.π C ((n+1 : ℕ) : ℤ))) = 0 := by
    rw [completeResolutionTail_d]
    apply ModuleCat.hom_ext
    change (f.comp (CokerAt.π C ((n+1 : ℕ) : ℤ))).comp
      (C.d (((n+1)+1 : ℕ) : ℤ) ((n+1 : ℕ) : ℤ)).hom = 0
    rw [show (((n+1)+1 : ℕ) : ℤ) = ((n+1 : ℕ) : ℤ)+1 by omega]
    exact hz
  change (Q C hC proj).extMk (ModuleCat.ofHom (f.comp (CokerAt.π C ((n+1 : ℕ) : ℤ))))
    (n+2) rfl hf = 0 ↔ _
  have hab := hC.factors_iff_boundary (k := k) fin proj ((n+1 : ℕ) : ℤ)
    (f.comp (CokerAt.π C ((n+1 : ℕ) : ℤ))) hz
  rw [hdesc, show ((n+1 : ℕ) : ℤ)-1 = (n : ℤ) by omega] at hab
  erw [(Q C hC proj).extMk_eq_zero_iff _ _ _ _ n rfl, hab]
  constructor
  · rintro ⟨g,hg⟩
    rw [completeResolutionTail_d] at hg
    exact ⟨g.hom,ModuleCat.hom_ext_iff.mp hg⟩
  · rintro ⟨g,hg⟩
    refine ⟨ModuleCat.ofHom g,?_⟩
    rw [completeResolutionTail_d]
    exact ModuleCat.hom_ext hg

def equiv (n : ℕ) :
    StableHom (k := k) (R := R) (M := CokerAt C ((n+1 : ℕ) : ℤ)) (N := N) ≃ₗ[k]
      Ext (ModuleCat.of R (CokerAt C 0)) N (n+1) := by
  change ((CokerAt C ((n+1 : ℕ) : ℤ) →ₗ[R] N) ⧸ projectiveFactors (k := k)) ≃ₗ[k] _
  rw [← toExt_kernel C hC fin proj N n]
  exact (toExt C hC proj N (n+1)).quotKerEquivOfSurjective
    (toExt_surjective C hC proj N (n+1))

end CompleteStableExt
end Tachikawa



namespace Tachikawa.Construction
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)
  (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)

abbrev selfHom := completeHom (k := k) (xComplete q) (xObj q)

def positiveSelfHomExt (n : ℕ) : VectorSplit.H (selfHom q) ((n+1:ℕ):ℤ) ≃ₗ[k]
    Ext (xObj q) (xObj q) (n+1) :=
  (CompleteHom.equiv (xComplete q) (xObj q)
    ((finiteX q).complete_totallyAcyclic (formE q))
    ((finiteX q).complete_finite (formE q)) ((finiteX q).complete_projective (formE q)) _).trans
  ((CompleteStableExt.equiv _ ((finiteX q).complete_totallyAcyclic (formE q))
    ((finiteX q).complete_finite (formE q)) ((finiteX q).complete_projective (formE q))
    (xObj q) n).trans (extIso (k := k) ((finiteX q).cokerEquiv (formE q)).toModuleIso
    (Iso.refl _) (n+1)))

include hq hp in
lemma positiveSelfHom_zero (n : ℕ) (hn : (n+1)%3 ≠ 0) :
    Subsingleton (VectorSplit.H (selfHom q) ((n+1:ℕ):ℤ)) := by
  let := XExt_zero_off_multiples q hq hp (n+1) hn
  have he := extIso (k := k) (XTensorIso q).symm (XTensorIso q).symm (n+1)
  let : Subsingleton (Ext (xObj q) (xObj q) (n+1)) := he.injective.subsingleton
  exact (positiveSelfHomExt q n).injective.subsingleton

def selfHomDual (a : ℤ) : VectorSplit.H (selfHom q) a ≃ₗ[k]
    Module.Dual k (VectorSplit.H (selfHom q) (-a-1)) := by
  let P := xComplete q
  let ce := (finiteX q).cokerEquiv (formE q)
  let ta := (finiteX q).complete_totallyAcyclic (formE q)
  let fin := (finiteX q).complete_finite (formE q)
  let proj := (finiteX q).complete_projective (formE q)
  let e₁ := CompleteHom.equiv (k := k) P (xObj q) ta fin proj a
  let e₂ := (StableEquiv.ofLinearEquiv (k := k)
    (M := ModuleCat.of (E q) (CokerAt P 0)) (N := xObj q) ce).symm.post
      (ModuleCat.of (E q) (CokerAt P a))
  have e₃ := cokerStableHomTranslate P ta.1 P ta.1 fin proj fin proj a 0 (-a) (k := k)
  rw [add_neg_cancel,zero_add] at e₃
  let e₄ := (StableEquiv.ofLinearEquiv (k := k)
    (M := ModuleCat.of (E q) (CokerAt P 0)) (N := xObj q) ce).pre
      (ModuleCat.of (E q) (CokerAt P (-a)))
  have e₅ := completeCokerDuality (formE q) P ta.1 fin proj (-a-1) (xObj q)
  rw [show -a-1+1 = -a by omega] at e₅
  exact e₁.trans (e₂.trans (e₃.trans (e₄.trans
    (e₅.trans (CompleteHom.equiv (k := k) P (xObj q) ta fin proj (-a-1)).dualMap))))

omit [CharP k 2] in
lemma selfHom_zero_of_dual (a : ℤ) (h : Subsingleton (VectorSplit.H (selfHom q) (-a-1))) :
    Subsingleton (VectorSplit.H (selfHom q) a) := by
  let := h
  let : Subsingleton (Module.Dual k (VectorSplit.H (selfHom q) (-a-1))) := by
    constructor
    intro f g
    apply LinearMap.ext
    intro x
    rw [Subsingleton.elim x 0,map_zero,map_zero]
  exact (selfHomDual q a).injective.subsingleton

include hq hp in
lemma selfHom_zero_near : Subsingleton (VectorSplit.H (selfHom q) 1) ∧
    Subsingleton (VectorSplit.H (selfHom q) 2) ∧
    Subsingleton (VectorSplit.H (selfHom q) (-2)) ∧
    Subsingleton (VectorSplit.H (selfHom q) (-3)) := by
  have h1 := positiveSelfHom_zero q hq hp 0 (by decide)
  have h2 := positiveSelfHom_zero q hq hp 1 (by decide)
  exact ⟨h1,h2,selfHom_zero_of_dual q (-2) h1,selfHom_zero_of_dual q (-3) h2⟩

omit [CharP k 2] in
lemma XEnd_scalar (f : xObj q →ₗ[E q] xObj q) :
    f = (show k from f (1 : k)) • LinearMap.id := by
  apply LinearMap.ext
  intro x
  have h := f.map_smul (algebraMap k (E q) (show k from x)) (1:k)
  change f ((characterE q (algebraMap k (E q) (show k from x))) * 1) =
    (characterE q (algebraMap k (E q) (show k from x))) * (show k from f (1:k)) at h
  erw [(characterE q).commutes,Algebra.algebraMap_self,mul_one] at h
  change f x = (characterE q (algebraMap k (E q) (show k from f (1:k)))) * (show k from x)
  rw [(characterE q).commutes,Algebra.algebraMap_self]
  exact h.trans (mul_comm (show k from x) (show k from f (1:k)))

include hq hp in
def stableXEndEquiv : StableMap (k := k) (xObj q) (xObj q) ≃ₗ[k] k := by
  let : Module.Finite (E q) (xObj q) := (finiteX q).finite
  let v := stableClass (k := k) (LinearMap.id (R := E q) (M := xObj q))
  have hv : v ≠ 0 := (stable_id_ne_zero_iff (k := k)).mpr (X_nonprojective q hq hp)
  let f := LinearMap.toSpanSingleton k _ v
  apply (LinearEquiv.ofBijective f ?_).symm
  constructor
  · apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro c hc
    exact (smul_eq_zero.mp hc).resolve_right hv
  · intro x
    obtain ⟨g,rfl⟩ := stableClass_surjective x
    use (show k from g (1:k))
    conv_rhs => rw [XEnd_scalar q g,map_smul]
    rfl

def selfHomZeroEquiv : VectorSplit.H (selfHom q) 0 ≃ₗ[k] k :=
  (CompleteHom.zeroEquiv (xComplete q) ((finiteX q).complete_totallyAcyclic (formE q))
    ((finiteX q).complete_finite (formE q)) ((finiteX q).complete_projective (formE q))
    (X := xObj q) ((finiteX q).cokerEquiv (formE q)) (xObj q)).trans (stableXEndEquiv q hq hp)
end Tachikawa.Construction



namespace Tachikawa.Construction
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q H : k) (hH : H ≠ 0)
  (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)

abbrev xTwistHom : selfHom q ⟶ selfHom q :=
  (finiteX q).completeTwistHom (formE q) (sigma q H hH) (XTwistIso q H hH)

include hq hp in
lemma xTwistHom_positive (n : ℕ) (x : VectorSplit.H (selfHom q) ((n+1:ℕ):ℤ)) :
    VectorSplit.Hmap (xTwistHom q H hH) _ x = (H⁻¹)^((n+1)/3) • x :=
  (finiteX q).completeTwistHom_positive (formE q) (sigma q H hH) (XTwistIso q H hH)
    n _ (XTwist_weight q H hH hq hp (n+1)) x

include hq hp in
lemma xTwistHom_negative (n : ℕ) (x : VectorSplit.H (selfHom q) (Int.negSucc (n+1))) :
    VectorSplit.Hmap (xTwistHom q H hH) _ x = (H^2*H^((n+1)/3)) • x := by
  apply (finiteX q).completeTwistHom_negative (formE q) (sigma q H hH) (XTwistIso q H hH)
    (fun x => by rw [XTwistIso_hom]; rfl) (XInverseTwistIso q H hH)
    (XInverseTwistIso_hom_apply q H hH) n (H^2) (H^((n+1)/3))
  · exact formE_sigma q H hH
  · exact XInverseTwist_weight q H hH hq hp (n+1)

end Tachikawa.Construction

end

end OAI
