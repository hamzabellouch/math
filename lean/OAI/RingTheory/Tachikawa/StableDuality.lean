import OAI.RingTheory.Tachikawa.Symmetry

namespace OAI


noncomputable section
namespace Tachikawa
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable {M N L : Type} [AddCommGroup M] [AddCommGroup N] [AddCommGroup L]
  [Module R M] [Module R N] [Module R L]
  [Module k M] [Module k N] [Module k L]
  [IsScalarTower k R M] [IsScalarTower k R N] [IsScalarTower k R L]

def projectiveFactors : Submodule k (M →ₗ[R] N) where
  carrier f := ∃ P : ModuleCat.{0} R, Module.Finite R P ∧ Module.Projective R P ∧
    ∃ i : M →ₗ[R] P, ∃ p : P →ₗ[R] N, p.comp i = f
  zero_mem' := ⟨ModuleCat.of R R, inferInstance, inferInstance, 0, 0, by simp⟩
  add_mem' {f g} hf hg := by
    obtain ⟨P, hPf, hPp, i, p, rfl⟩ := hf
    obtain ⟨Q, hQf, hQp, j, q, rfl⟩ := hg
    let := hPf
    let := hPp
    let := hQf
    let := hQp
    refine ⟨ModuleCat.of R (P × Q), inferInstance, inferInstance,
      i.prod j, p.coprod q, ?_⟩
    ext x
    rfl
  smul_mem' c f hf := by
    obtain ⟨P, hPf, hPp, i, p, rfl⟩ := hf
    exact ⟨P, hPf, hPp, i, c • p, by ext x; rfl⟩

omit [Module k M] [IsScalarTower k R M] in
lemma mem_projectiveFactors_iff (f : M →ₗ[R] N) :
    f ∈ projectiveFactors (k := k) ↔
    ∃ P : ModuleCat.{0} R, Module.Finite R P ∧ Module.Projective R P ∧
      ∃ i : M →ₗ[R] P, ∃ p : P →ₗ[R] N, p.comp i = f := Iff.rfl

omit [Module k M] [Module k L] [IsScalarTower k R M] [IsScalarTower k R L] in
lemma projectiveFactors_precomp {f : M →ₗ[R] N}
    (hf : f ∈ projectiveFactors (k := k)) (g : L →ₗ[R] M) :
    f.comp g ∈ projectiveFactors (k := k) := by
  obtain ⟨P, hPf, hPp, i, p, rfl⟩ := hf
  exact ⟨P, hPf, hPp, i.comp g, p, rfl⟩

omit [Module k M] [IsScalarTower k R M] in
lemma projectiveFactors_postcomp {f : M →ₗ[R] N}
    (hf : f ∈ projectiveFactors (k := k)) (g : N →ₗ[R] L) :
    g.comp f ∈ projectiveFactors (k := k) := by
  obtain ⟨P, hPf, hPp, i, p, rfl⟩ := hf
  exact ⟨P, hPf, hPp, i, g.comp p, rfl⟩

lemma id_mem_projectiveFactors_iff [Module.Finite R M] :
    LinearMap.id (R := R) (M := M) ∈ projectiveFactors (k := k) ↔ Module.Projective R M := by
  constructor
  · rintro ⟨P, -, hPp, i, p, hp⟩
    let := hPp
    exact Module.Projective.of_split i p hp
  · intro h
    exact ⟨ModuleCat.of R M, inferInstance, h, LinearMap.id, LinearMap.id, rfl⟩

def StableHom := (M →ₗ[R] N) ⧸ projectiveFactors (k := k)

instance : AddCommGroup (StableHom (k := k) (R := R) (M := M) (N := N)) :=
  inferInstanceAs (AddCommGroup ((M →ₗ[R] N) ⧸ projectiveFactors (k := k)))
instance : Module k (StableHom (k := k) (R := R) (M := M) (N := N)) :=
  inferInstanceAs (Module k ((M →ₗ[R] N) ⧸ projectiveFactors (k := k)))

def stableClass : (M →ₗ[R] N) →ₗ[k] StableHom (k := k) (R := R) (M := M) (N := N) :=
  (projectiveFactors (k := k)).mkQ

omit [Module k M] [IsScalarTower k R M] in
lemma stableClass_eq_zero_iff (f : M →ₗ[R] N) :
    stableClass (k := k) f = 0 ↔ f ∈ projectiveFactors (k := k) :=
  Submodule.Quotient.mk_eq_zero _

lemma stable_id_ne_zero_iff [Module.Finite R M] :
    stableClass (k := k) (LinearMap.id (R := R) (M := M)) ≠ 0 ↔ ¬ Module.Projective R M := by
  rw [ne_eq, stableClass_eq_zero_iff, id_mem_projectiveFactors_iff]

def stablePostcompose (g : N →ₗ[R] L) :
    StableHom (k := k) (R := R) (M := M) (N := N) →ₗ[k]
      StableHom (k := k) (R := R) (M := M) (N := L) :=
  (projectiveFactors (k := k)).mapQ (projectiveFactors (k := k))
    { toFun := fun f => g.comp f
      map_add' := fun f f' => by ext x; simp
      map_smul' := fun c f => by ext x; simp }
    (fun _ hf => projectiveFactors_postcomp hf g)

omit [Module k M] [IsScalarTower k R M] in
@[simp] lemma stablePostcompose_class (g : N →ₗ[R] L) (f : M →ₗ[R] N) :
    stablePostcompose (k := k) g (stableClass (k := k) f) =
      stableClass (k := k) (g.comp f) := rfl

omit [Module k M] [IsScalarTower k R M] in
lemma stableClass_surjective : Function.Surjective
    (stableClass (k := k) (R := R) (M := M) (N := N)) :=
  Submodule.mkQ_surjective _

def stablePostcomposeLinear : (N →ₗ[R] L) →ₗ[k]
    (StableHom (k := k) (R := R) (M := M) (N := N) →ₗ[k]
      StableHom (k := k) (R := R) (M := M) (N := L)) where
  toFun := stablePostcompose
  map_add' g g' := by
    apply LinearMap.ext
    intro x
    obtain ⟨f, rfl⟩ := stableClass_surjective x
    change stableClass (k := k) ((g+g').comp f) =
      stableClass (k := k) (g.comp f) + stableClass (k := k) (g'.comp f)
    rw [LinearMap.add_comp, map_add]
  map_smul' c g := by
    apply LinearMap.ext
    intro x
    obtain ⟨f, rfl⟩ := stableClass_surjective x
    change stableClass (k := k) ((c • g).comp f) = c • stableClass (k := k) (g.comp f)
    rw [LinearMap.smul_comp, map_smul]

def stableComp : StableHom (k := k) (R := R) (M := N) (N := L) →ₗ[k]
    (StableHom (k := k) (R := R) (M := M) (N := N) →ₗ[k]
      StableHom (k := k) (R := R) (M := M) (N := L)) :=
  (projectiveFactors (k := k)).liftQ stablePostcomposeLinear (by
    intro g hg
    apply LinearMap.ext
    intro x
    obtain ⟨f, rfl⟩ := stableClass_surjective x
    change stableClass (k := k) (g.comp f) = 0
    exact (stableClass_eq_zero_iff _).mpr (projectiveFactors_precomp hg f))

omit [Module k M] [IsScalarTower k R M] in
@[simp] lemma stableComp_class (g : N →ₗ[R] L) (f : M →ₗ[R] N) :
    stableComp (k := k) (stableClass (k := k) g) (stableClass (k := k) f) =
      stableClass (k := k) (g.comp f) := rfl

instance [FiniteDimensional k M] [FiniteDimensional k N] :
    FiniteDimensional k (StableHom (k := k) (R := R) (M := M) (N := N)) := by
  let : FiniteDimensional k (M →ₗ[R] N) :=
    Module.Finite.of_injective (LinearMap.restrictScalarsₗ k R M N k)
      (LinearMap.restrictScalars_injective k)
  exact Module.Finite.of_surjective stableClass stableClass_surjective

end Tachikawa



namespace Tachikawa
variable {R M P : Type} [Ring R] [AddCommGroup M] [Module R M]
  [AddCommGroup P] [Module R P]

lemma injective_of_retract [Module.Injective R P]
    (i : M →ₗ[R] P) (s : P →ₗ[R] M) (hs : s.comp i = LinearMap.id) :
    Module.Injective R M := by
  constructor
  intro X Y _ _ _ _ f hf g
  obtain ⟨h, hh⟩ := Module.Injective.extension_property R P X Y f hf (i.comp g)
  refine ⟨s.comp h, ?_⟩
  intro x
  change s (h (f x)) = g x
  have hhx : h (f x) = i (g x) := LinearMap.congr_fun hh x
  rw [hhx]
  exact LinearMap.congr_fun hs (g x)

lemma injective_of_finite_projective [Module.Injective R R]
    [Module.Finite R M] [Module.Projective R M] : Module.Injective R M := by
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  exact injective_of_retract g f hfg

variable {k : Type} [Field k] [Algebra k R] [FiniteDimensional k R]
  [Module k M] [IsScalarTower k R M] [FiniteDimensional k M]

def finiteCoinducedEmbedding : M →ₗ[R] (Fin (Module.finrank k M) → DualBimodule k R) :=
  LinearMap.pi (fun i => DualBimodule.coinduce ((Module.finBasis k M).coord i))

omit [FiniteDimensional k R] in
lemma finiteCoinducedEmbedding_injective :
    Function.Injective (finiteCoinducedEmbedding (k := k) (R := R) (M := M)) := by
  intro x y h
  apply (Module.finBasis k M).repr.injective
  ext i
  have hi := congrArg (fun F : Fin (Module.finrank k M) → DualBimodule k R => F i 1) h
  simpa only [finiteCoinducedEmbedding, LinearMap.pi_apply, DualBimodule.coinduce_apply,
    one_smul, Module.Basis.coord_apply] using hi

lemma projective_of_finite_injective (t : SymmetrizingForm (k := k) (R := R))
    [Module.Injective R M] : Module.Projective R M := by
  let : Module.Projective R (Fin (Module.finrank k M) → DualBimodule k R) :=
    Module.Projective.of_equiv
      (LinearEquiv.piCongrRight (fun _ : Fin (Module.finrank k M) => t.dualEquiv))
  let i := finiteCoinducedEmbedding (k := k) (R := R) (M := M)
  obtain ⟨s, hs⟩ := Module.Injective.extension_property R M M _ i
    finiteCoinducedEmbedding_injective LinearMap.id
  exact Module.Projective.of_split i s hs

end Tachikawa



namespace Tachikawa
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable {M N P : Type} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [Module R M] [Module R N] [Module R P]
  [Module k M] [Module k N] [Module k P]
  [IsScalarTower k R M] [IsScalarTower k R N] [IsScalarTower k R P]

def homPrecompose (i : M →ₗ[R] P) : (P →ₗ[R] N) →ₗ[k] (M →ₗ[R] N) where
  toFun f := f.comp i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def homPostcompose (p : P →ₗ[R] N) : (M →ₗ[R] P) →ₗ[k] (M →ₗ[R] N) where
  toFun f := p.comp f
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

omit [Module k M] [Module k P] [IsScalarTower k R M] [IsScalarTower k R P] in

lemma factors_iff_extends [Module.Injective R R]
    [Module.Finite R P] [Module.Projective R P]
    (i : M →ₗ[R] P) (hi : Function.Injective i) (f : M →ₗ[R] N) :
    f ∈ projectiveFactors (k := k) ↔ ∃ g : P →ₗ[R] N, g.comp i = f := by
  constructor
  · rintro ⟨J, hJf, hJp, a, b, rfl⟩
    let := hJf
    let := hJp
    let : Module.Injective R J := injective_of_finite_projective
    obtain ⟨a', ha'⟩ := Module.Injective.extension_property R J M P i hi a
    refine ⟨b.comp a', ?_⟩
    rw [LinearMap.comp_assoc, ha']
  · rintro ⟨g, rfl⟩
    exact ⟨ModuleCat.of R P, inferInstance, inferInstance, i, g, rfl⟩

omit [Module k M] [Module k P] [IsScalarTower k R M] [IsScalarTower k R P] in

lemma factors_iff_lifts [Module.Finite R P] [Module.Projective R P]
    (p : P →ₗ[R] N) (hp : Function.Surjective p) (f : M →ₗ[R] N) :
    f ∈ projectiveFactors (k := k) ↔ ∃ g : M →ₗ[R] P, p.comp g = f := by
  constructor
  · rintro ⟨J, hJf, hJp, a, b, rfl⟩
    let := hJp
    obtain ⟨b', hb'⟩ := Module.projective_lifting_property p b hp
    exact ⟨b'.comp a, by rw [← LinearMap.comp_assoc, hb']⟩
  · rintro ⟨g, rfl⟩
    exact ⟨ModuleCat.of R P, inferInstance, inferInstance, g, p, rfl⟩

omit [Module k M] [Module k P] [IsScalarTower k R M] [IsScalarTower k R P] in
lemma projectiveFactors_eq_range_precompose [Module.Injective R R]
    [Module.Finite R P] [Module.Projective R P]
    (i : M →ₗ[R] P) (hi : Function.Injective i) :
    projectiveFactors (k := k) (M := M) (N := N) = LinearMap.range (homPrecompose i) := by
  ext f
  exact factors_iff_extends i hi f

omit [Module k M] [IsScalarTower k R M] in
lemma projectiveFactors_eq_range_postcompose
    [Module.Finite R P] [Module.Projective R P]
    (p : P →ₗ[R] N) (hp : Function.Surjective p) :
    projectiveFactors (k := k) (M := M) = LinearMap.range (homPostcompose p) := by
  ext f
  exact factors_iff_lifts p hp f

end Tachikawa



namespace Tachikawa
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable {N : Type} [AddCommGroup N] [Module R N] [Module k N] [IsScalarTower k R N]
namespace SymmetrizingForm
variable (t : SymmetrizingForm (k := k) (R := R)) [FiniteDimensional k R]

def homDual : (N →ₗ[R] R) →ₗ[k] Module.Dual k N where
  toFun f := t.linear.comp (f.restrictScalars k)
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

omit [FiniteDimensional k R] in
@[simp] lemma homDual_apply (f : N →ₗ[R] R) (x : N) :
    t.homDual f x = t.linear (f x) := rfl

lemma homDual_bijective : Function.Bijective (t.homDual (N := N)) := by
  constructor
  · intro f g h
    ext x
    apply t.toDual_injective
    ext r
    change t.linear (r * f x) = t.linear (r * g x)
    have hr := LinearMap.congr_fun h (r • x)
    simpa only [homDual_apply, map_smul, smul_eq_mul] using hr
  · intro l
    refine ⟨t.dualEquiv.symm.toLinearMap.comp (DualBimodule.coinduce l), ?_⟩
    ext x
    have h := congrArg (fun z : DualBimodule k R => z 1)
      (t.dualEquiv.apply_symm_apply (DualBimodule.coinduce l x))
    change t.linear (1 * t.dualEquiv.symm (DualBimodule.coinduce l x)) = l (1 • x) at h
    simpa only [one_mul, one_smul, homDual_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe] using h

def homDualEquiv : (N →ₗ[R] R) ≃ₗ[k] Module.Dual k N :=
  LinearEquiv.ofBijective t.homDual t.homDual_bijective

@[simp] lemma homDualEquiv_apply (f : N →ₗ[R] R) (x : N) :
    t.homDualEquiv f x = t.linear (f x) := rfl

end SymmetrizingForm

def homPiEquiv (ι : Type) : (N →ₗ[R] (ι → R)) ≃ₗ[k] (ι → N →ₗ[R] R) where
  toFun f i := (LinearMap.proj i).comp f
  invFun := LinearMap.pi
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

namespace SymmetrizingForm
variable (t : SymmetrizingForm (k := k) (R := R)) [FiniteDimensional k R]
variable (ι : Type) [Fintype ι] [DecidableEq ι]

def freeHomDual : (N →ₗ[R] (ι → R)) ≃ₗ[k]
    Module.Dual k ((ι → R) →ₗ[R] N) :=
  (homPiEquiv ι).trans ((LinearEquiv.piCongrRight (fun _ : ι => t.homDualEquiv)).trans
    ((LinearMap.lsum k (fun _ : ι => N) k).trans
      (LinearEquiv.piRing R N ι k).dualMap))

@[simp] lemma freeHomDual_apply (g : N →ₗ[R] (ι → R)) (f : (ι → R) →ₗ[R] N) :
    t.freeHomDual ι g f = ∑ i, t.linear (g (f (Pi.single i 1)) i) := by
  simp [freeHomDual, homPiEquiv, LinearMap.lsum_apply]
  rfl

lemma freeHomDual_natural {N' : Type} [AddCommGroup N'] [Module R N'] [Module k N']
    [IsScalarTower k R N'] (g : N' →ₗ[R] (ι → R))
    (a : N →ₗ[R] N') (f : (ι → R) →ₗ[R] N) :
    t.freeHomDual ι (g.comp a) f = t.freeHomDual ι g (a.comp f) := by
  simp only [freeHomDual_apply, LinearMap.comp_apply]

lemma freeHomDual_cyclic (g : N →ₗ[R] (ι → R))
    (f : (ι → R) →ₗ[R] N) (a : (ι → R) →ₗ[R] (ι → R)) :
    t.freeHomDual ι g (f.comp a) = t.freeHomDual ι (a.comp g) f := by
  have expand (h : (ι → R) →ₗ[R] N) (x : ι → R) :
      h x = ∑ i, x i • h (Pi.single i 1) := by
    simpa only [LinearEquiv.piRing_symm_apply, LinearEquiv.piRing_apply] using
      (congrArg (fun z : (ι → R) →ₗ[R] N => z x)
        ((LinearEquiv.piRing R N ι k).symm_apply_apply h)).symm
  have expand' (x : ι → R) : a x = ∑ i, x i • a (Pi.single i 1) := by
    simpa only [LinearEquiv.piRing_symm_apply, LinearEquiv.piRing_apply] using
      (congrArg (fun z : (ι → R) →ₗ[R] (ι → R) => z x)
        ((LinearEquiv.piRing R (ι → R) ι k).symm_apply_apply a)).symm
  simp only [freeHomDual_apply, LinearMap.comp_apply]
  conv_lhs => arg 2; ext j; rw [expand f (a (Pi.single j 1))]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  conv_rhs => arg 2; ext j; rw [expand' (g (f (Pi.single j 1)))]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact t.comm _ _

lemma freeHomDual_cyclic_rect (κ : Type) [Fintype κ] [DecidableEq κ]
    (g : N →ₗ[R] (κ → R)) (f : (ι → R) →ₗ[R] N)
    (a : (κ → R) →ₗ[R] (ι → R)) :
    t.freeHomDual κ g (f.comp a) = t.freeHomDual ι (a.comp g) f := by
  have expand (x : ι → R) : f x = ∑ i, x i • f (Pi.single i 1) := by
    simpa only [LinearEquiv.piRing_symm_apply, LinearEquiv.piRing_apply] using
      (congrArg (fun z : (ι → R) →ₗ[R] N => z x)
        ((LinearEquiv.piRing R N ι k).symm_apply_apply f)).symm
  have expand' (x : κ → R) : a x = ∑ j, x j • a (Pi.single j 1) := by
    simpa only [LinearEquiv.piRing_symm_apply, LinearEquiv.piRing_apply] using
      (congrArg (fun z : (κ → R) →ₗ[R] (ι → R) => z x)
        ((LinearEquiv.piRing R (ι → R) κ k).symm_apply_apply a)).symm
  simp only [freeHomDual_apply, LinearMap.comp_apply]
  conv_lhs => arg 2; ext j; rw [expand (a (Pi.single j 1))]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  conv_rhs => arg 2; ext j; rw [expand' (g (f (Pi.single j 1)))]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact t.comm _ _

end SymmetrizingForm
end Tachikawa



namespace Tachikawa
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]
variable {M N : Type} [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module R N] [Module k N]
  [IsScalarTower k R N]
namespace SymmetrizingForm
variable (t : SymmetrizingForm (k := k) (R := R))
variable {n : ℕ} (ε : (Fin n → R) →ₗ[R] M)

def syzygyPair : (N →ₗ[R] LinearMap.ker ε) →ₗ[k] Module.Dual k (M →ₗ[R] N) :=
  (homPrecompose (k := k) ε).dualMap.comp
    ((t.freeHomDual (Fin n)).toLinearMap.comp (homPostcompose (LinearMap.ker ε).subtype))

lemma syzygyPair_apply (g : N →ₗ[R] LinearMap.ker ε) (f : M →ₗ[R] N) :
    t.syzygyPair ε g f = t.freeHomDual (Fin n) ((LinearMap.ker ε).subtype.comp g)
      (f.comp ε) := rfl

lemma syzygyPair_vanish_left {m : ℕ} (i : M →ₗ[R] (Fin m → R))
    (hi : Function.Injective i) (g : N →ₗ[R] LinearMap.ker ε)
    (f : M →ₗ[R] N) (hf : f ∈ projectiveFactors (k := k)) :
    t.syzygyPair ε g f = 0 := by
  let : Module.Injective R R := t.injective
  obtain ⟨a, rfl⟩ := (factors_iff_extends i hi f).mp hf
  rw [syzygyPair_apply, LinearMap.comp_assoc, t.freeHomDual_cyclic_rect]
  have hzero : (i.comp ε).comp ((LinearMap.ker ε).subtype.comp g) = 0 := by
    apply LinearMap.ext
    intro x
    change i (ε (g x).val) = 0
    rw [(g x).property, map_zero]
  rw [hzero, map_zero, LinearMap.zero_apply]

lemma syzygyPair_vanish_right {p : ℕ}
    (d : (Fin p → R) →ₗ[R] LinearMap.ker ε) (hd : Function.Surjective d)
    (g : N →ₗ[R] LinearMap.ker ε) (hg : g ∈ projectiveFactors (k := k)) :
    t.syzygyPair ε g = 0 := by
  obtain ⟨a, rfl⟩ := (factors_iff_lifts d hd g).mp hg
  ext f
  rw [syzygyPair_apply, ← LinearMap.comp_assoc, ← t.freeHomDual_cyclic_rect]
  have hzero : (f.comp ε).comp ((LinearMap.ker ε).subtype.comp d) = 0 := by
    apply LinearMap.ext
    intro x
    change f (ε (d x).val) = 0
    rw [(d x).property, map_zero]
  rw [hzero, map_zero]
  rfl

def syzygyPairOnStable {m : ℕ} (i : M →ₗ[R] (Fin m → R))
    (hi : Function.Injective i) :
    (N →ₗ[R] LinearMap.ker ε) →ₗ[k]
      Module.Dual k (StableHom (k := k) (R := R) (M := M) (N := N)) where
  toFun g := (projectiveFactors (k := k)).liftQ (t.syzygyPair ε g)
    (by intro f hf; exact t.syzygyPair_vanish_left ε i hi g f hf)
  map_add' g h := by
    ext x
    obtain ⟨f, rfl⟩ := stableClass_surjective x
    change t.syzygyPair ε (g+h) f = t.syzygyPair ε g f + t.syzygyPair ε h f
    rw [map_add, LinearMap.add_apply]
  map_smul' c g := by
    ext x
    obtain ⟨f, rfl⟩ := stableClass_surjective x
    change t.syzygyPair ε (c • g) f = c • t.syzygyPair ε g f
    rw [map_smul, LinearMap.smul_apply]

lemma syzygyPairOnStable_apply {m : ℕ} (i : M →ₗ[R] (Fin m → R))
    (hi : Function.Injective i) (g : N →ₗ[R] LinearMap.ker ε) (f : M →ₗ[R] N) :
    t.syzygyPairOnStable ε i hi g (stableClass (k := k) f) = t.syzygyPair ε g f := rfl

def stableDualMap {m p : ℕ} (i : M →ₗ[R] (Fin m → R))
    (hi : Function.Injective i) (d : (Fin p → R) →ₗ[R] LinearMap.ker ε)
    (hd : Function.Surjective d) :
    StableHom (k := k) (R := R) (M := N) (N := LinearMap.ker ε) →ₗ[k]
      Module.Dual k (StableHom (k := k) (R := R) (M := M) (N := N)) :=
  (projectiveFactors (k := k)).liftQ (t.syzygyPairOnStable ε i hi)
    (by
      intro g hg
      ext x
      obtain ⟨f, rfl⟩ := stableClass_surjective x
      change t.syzygyPair ε g f = 0
      rw [t.syzygyPair_vanish_right ε d hd g hg, LinearMap.zero_apply])

lemma stableDualMap_apply {m p : ℕ} (i : M →ₗ[R] (Fin m → R))
    (hi : Function.Injective i) (d : (Fin p → R) →ₗ[R] LinearMap.ker ε)
    (hd : Function.Surjective d) (g : N →ₗ[R] LinearMap.ker ε) (f : M →ₗ[R] N) :
    t.stableDualMap ε i hi d hd (stableClass (k := k) g) (stableClass (k := k) f) =
      t.syzygyPair ε g f := rfl

omit [FiniteDimensional k R] in

lemma precompose_range_eq_ker (hε : Function.Surjective ε) {p : ℕ}
    (d : (Fin p → R) →ₗ[R] LinearMap.ker ε) (hd : Function.Surjective d) :
    LinearMap.range (homPrecompose (k := k) (N := N) ε) =
      LinearMap.ker (homPrecompose (k := k) (N := N) ((LinearMap.ker ε).subtype.comp d)) := by
  ext a
  constructor
  · rintro ⟨f, rfl⟩
    apply LinearMap.ext
    intro x
    change f (ε (d x).val) = 0
    rw [(d x).property, map_zero]
  · intro ha
    have hk : LinearMap.ker ε ≤ LinearMap.ker a := by
      intro x hx
      obtain ⟨y, hy⟩ := hd ⟨x, hx⟩
      have hy' : (d y).val = x := congrArg Subtype.val hy
      have hay := LinearMap.congr_fun ha y
      change a (d y).val = 0 at hay
      simpa only [LinearMap.mem_ker, ← hy'] using hay
    refine ⟨((LinearMap.ker ε).liftQ a hk).comp
      (ε.quotKerEquivOfSurjective hε).symm.toLinearMap, ?_⟩
    apply LinearMap.ext
    intro x
    change (LinearMap.ker ε).liftQ a hk ((ε.quotKerEquivOfSurjective hε).symm (ε x)) = a x
    rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
    rfl

lemma syzygyPair_eq_zero_iff (hε : Function.Surjective ε) {p : ℕ}
    (d : (Fin p → R) →ₗ[R] LinearMap.ker ε) (hd : Function.Surjective d)
    (g : N →ₗ[R] LinearMap.ker ε) :
    t.syzygyPair ε g = 0 ↔ g ∈ projectiveFactors (k := k) := by
  constructor
  · intro hg
    let δ := (LinearMap.ker ε).subtype.comp d
    let l := t.freeHomDual (Fin n) ((LinearMap.ker ε).subtype.comp g)
    have hl : l ∈ (LinearMap.ker (homPrecompose (k := k) (N := N) δ)).dualAnnihilator := by
      rw [← precompose_range_eq_ker ε hε d hd]
      rw [Submodule.mem_dualAnnihilator]
      rintro a ⟨f, rfl⟩
      exact LinearMap.congr_fun hg f
    rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hl
    obtain ⟨l', hl'⟩ := hl
    obtain ⟨a, rfl⟩ := (t.freeHomDual (Fin p) (N := N)).surjective l'
    have hga : (LinearMap.ker ε).subtype.comp g = δ.comp a := by
      apply (t.freeHomDual (Fin n)).injective
      ext f
      have hf := LinearMap.congr_fun hl' f
      change t.freeHomDual (Fin p) a (f.comp δ) = l f at hf
      rw [t.freeHomDual_cyclic_rect] at hf
      exact hf.symm
    apply (factors_iff_lifts d hd g).mpr
    refine ⟨a, ?_⟩
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact (LinearMap.congr_fun hga x).symm
  · exact t.syzygyPair_vanish_right ε d hd g

lemma stableDualMap_injective (hε : Function.Surjective ε) {m p : ℕ}
    (i : M →ₗ[R] (Fin m → R)) (hi : Function.Injective i)
    (d : (Fin p → R) →ₗ[R] LinearMap.ker ε) (hd : Function.Surjective d) :
    Function.Injective (t.stableDualMap (N := N) ε i hi d hd) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  obtain ⟨g, rfl⟩ := stableClass_surjective x
  apply (stableClass_eq_zero_iff g).mpr
  apply (t.syzygyPair_eq_zero_iff ε hε d hd g).mp
  ext f
  exact LinearMap.congr_fun hx (stableClass (k := k) f)

lemma stableDualMap_surjective (hε : Function.Surjective ε) {m p : ℕ}
    (i : M →ₗ[R] (Fin m → R)) (hi : Function.Injective i)
    (d : (Fin p → R) →ₗ[R] LinearMap.ker ε) (hd : Function.Surjective d) :
    Function.Surjective (t.stableDualMap (N := N) ε i hi d hd) := by
  intro l
  have hinj : Function.Injective (homPrecompose (k := k) (N := N) ε) := by
    intro f g h
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := hε x
    exact LinearMap.congr_fun h y
  obtain ⟨L, hL⟩ := LinearMap.dualMap_surjective_of_injective hinj
    (l.comp (stableClass (k := k)))
  obtain ⟨g₀, rfl⟩ := (t.freeHomDual (Fin n) (N := N)).surjective L
  have hzero : (i.comp ε).comp g₀ = 0 := by
    apply (t.freeHomDual (Fin m)).injective
    apply LinearMap.ext
    intro a
    rw [map_zero, LinearMap.zero_apply]
    rw [← t.freeHomDual_cyclic_rect]
    have ha := LinearMap.congr_fun hL (a.comp i)
    change t.freeHomDual (Fin n) g₀ ((a.comp i).comp ε) =
      l (stableClass (k := k) (a.comp i)) at ha
    rw [LinearMap.comp_assoc] at ha
    have hac : stableClass (k := k) (a.comp i) = 0 := by
      apply (stableClass_eq_zero_iff _).mpr
      exact ⟨ModuleCat.of R (Fin m → R), inferInstance, inferInstance, i, a, rfl⟩
    rw [ha, hac, map_zero]
  have hk (x : N) : g₀ x ∈ LinearMap.ker ε := by
    apply hi
    have hx := LinearMap.congr_fun hzero x
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply, map_zero] using hx
  let g : N →ₗ[R] LinearMap.ker ε := g₀.codRestrict (LinearMap.ker ε) hk
  refine ⟨stableClass (k := k) g, ?_⟩
  apply LinearMap.ext
  intro x
  obtain ⟨f, rfl⟩ := stableClass_surjective x
  exact LinearMap.congr_fun hL f

def stableDualEquiv (hε : Function.Surjective ε) {m p : ℕ}
    (i : M →ₗ[R] (Fin m → R)) (hi : Function.Injective i)
    (d : (Fin p → R) →ₗ[R] LinearMap.ker ε) (hd : Function.Surjective d) :
    StableHom (k := k) (R := R) (M := N) (N := LinearMap.ker ε) ≃ₗ[k]
      Module.Dual k (StableHom (k := k) (R := R) (M := M) (N := N)) :=
  LinearEquiv.ofBijective (t.stableDualMap ε i hi d hd)
    ⟨t.stableDualMap_injective ε hε i hi d hd,
      t.stableDualMap_surjective ε hε i hi d hd⟩

end SymmetrizingForm
end Tachikawa



namespace Tachikawa
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable {M : Type} [AddCommGroup M] [Module R M]

structure FiniteFreeCover (R M : Type) [Ring R] [AddCommGroup M] [Module R M] where
  rank : ℕ
  map : (Fin rank → R) →ₗ[R] M
  surjective : Function.Surjective map

def finiteFreeCover [Module.Finite R M] : FiniteFreeCover R M :=
  let data := Module.Finite.exists_fin' R M
  ⟨data.choose, data.choose_spec.choose, data.choose_spec.choose_spec⟩

namespace SymmetrizingForm
variable [FiniteDimensional k R] (t : SymmetrizingForm (k := k) (R := R))
variable [Module k M] [IsScalarTower k R M] [FiniteDimensional k M]

def freeEmbedding : M →ₗ[R] (Fin (Module.finrank k M) → R) :=
  (LinearEquiv.piCongrRight (fun _ : Fin (Module.finrank k M) =>
    t.dualEquiv.symm)).toLinearMap.comp (finiteCoinducedEmbedding (k := k) (R := R))

lemma freeEmbedding_injective : Function.Injective (t.freeEmbedding (M := M)) :=
  (LinearEquiv.piCongrRight (fun _ : Fin (Module.finrank k M) =>
    t.dualEquiv.symm)).injective.comp finiteCoinducedEmbedding_injective

include t in

theorem exists_stableDualEquiv {N : Type} [AddCommGroup N] [Module R N]
    [Module k N] [IsScalarTower k R N] :
    ∃ (n : ℕ) (ε : (Fin n → R) →ₗ[R] M), Function.Surjective ε ∧
      Nonempty (StableHom (k := k) (R := R) (M := N) (N := LinearMap.ker ε) ≃ₗ[k]
        Module.Dual k (StableHom (k := k) (R := R) (M := M) (N := N))) := by
  let : Module.Finite R M := Module.Finite.of_restrictScalars_finite k R M
  let c := finiteFreeCover (R := R) (M := M)
  let : Module.Finite k (LinearMap.ker c.map) :=
    Module.Finite.of_injective ((LinearMap.ker c.map).subtype.restrictScalars k)
      Subtype.val_injective
  let : Module.Finite R (LinearMap.ker c.map) :=
    Module.Finite.of_restrictScalars_finite k R (LinearMap.ker c.map)
  let d := finiteFreeCover (R := R) (M := LinearMap.ker c.map)
  exact ⟨c.rank, c.map, c.surjective,
    ⟨SymmetrizingForm.stableDualEquiv t c.map c.surjective t.freeEmbedding t.freeEmbedding_injective
      d.map d.surjective⟩⟩

end SymmetrizingForm
end Tachikawa



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits

variable {R : Type*} [Ring R]

def resolutionOfExact (M : ModuleCat R) (P : ℕ → ModuleCat R)
    (d : ∀ n, P (n+1) ⟶ P n) (ε : P 0 ⟶ M)
    (hd : ∀ n, Function.Exact (d (n+1)) (d n))
    (hε : Function.Exact (d 0) ε) (surj : Function.Surjective ε)
    (proj : ∀ n, Projective (P n)) : ProjectiveResolution M := by
  let sq : ∀ n, d (n+1) ≫ d n = 0 := fun n => ModuleCat.hom_ext <| LinearMap.ext <|
    (hd n).apply_apply_eq_zero
  let K := ChainComplex.of P d sq
  let π : K ⟶ (ChainComplex.single₀ (ModuleCat R)).obj M :=
    (ChainComplex.toSingle₀Equiv _ _).symm ⟨ε, by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      exact hε.apply_apply_eq_zero⟩
  refine {complex := K, π := π, projective := proj, quasiIso := ⟨fun n => ?_⟩}
  cases n with
  | zero =>
    rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros' _ (by rfl) (by simp; rfl) (by rfl)]
    · constructor
      · apply (ShortComplex.moduleCat_exact_iff _).2
        change ∀ x : P 0, ε x = 0 → ∃ y : P 1, K.d 1 0 y = x
        have hk : K.d 1 0 = d 0 := ChainComplex.of_d P d 0
        rw [hk]
        exact fun x => (hε x).mp
      · change Epi ε
        exact (ModuleCat.epi_iff_surjective ε).2 surj
  | succ n =>
    rw [quasiIsoAt_iff_exactAt']
    · rw [HomologicalComplex.exactAt_iff' _ (n+2) (n+1) n (by simp) (by simp)]
      apply (ShortComplex.moduleCat_exact_iff _).2
      change ∀ x : P (n+1), K.d (n+1) n x = 0 → ∃ y, K.d (n+2) (n+1) y = x
      have hk₁ : K.d (n+1) n = d n := ChainComplex.of_d _ _ _
      have hk₂ : K.d (n+2) (n+1) = d (n+1) := ChainComplex.of_d _ _ _
      rw [hk₁, hk₂]
      exact fun x => (hd n x).mp
    · exact ChainComplex.exactAt_succ_single_obj _ _

end Tachikawa



namespace Tachikawa
open CategoryTheory

theorem ext_subsingleton_of_boundaries {C : Type*} [Category C] [Abelian C] [HasExt C]
    {X Y : C} (P : ProjectiveResolution X) (n : ℕ)
    (h : ∀ f : P.complex.X (n+1) ⟶ Y,
      P.complex.d (n+2) (n+1) ≫ f = 0 →
      ∃ g : P.complex.X n ⟶ Y, P.complex.d (n+1) n ≫ g = f) :
    Subsingleton (Abelian.Ext X Y (n+1)) := by
  have hzero (α : Abelian.Ext X Y (n+1)) : α = 0 := by
    obtain ⟨f, hf, rfl⟩ := P.extMk_surjective α (n+2) rfl
    exact (P.extMk_eq_zero_iff f (n+2) rfl hf n rfl).mpr (h f hf)
  exact ⟨fun α β => (hzero α).trans (hzero β).symm⟩

end Tachikawa

end

end OAI
