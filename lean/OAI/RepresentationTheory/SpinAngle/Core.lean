import Mathlib

namespace OAI



noncomputable section
open scoped BigOperators ComplexConjugate InnerProductSpace

namespace SpinAngle.Specht

variable {G : Type*} [contextInstance10_21 : Group G]
variable {E : Type*} [contextInstance11_21 : NormedAddCommGroup E] [contextInstance11_44 : InnerProductSpace ℂ E]


def cyclic (ρ : Representation ℂ G E) (e : E) : Subrepresentation ρ where
  toSubmodule := Submodule.span ℂ (Set.range fun g => ρ g e)
  apply_mem_toSubmodule g := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨h, rfl⟩ := hv
      exact Submodule.subset_span ⟨g * h, by simp⟩
    | zero => simp
    | add x y hx hy ihx ihy =>
      simpa using (Submodule.span ℂ (Set.range fun h => ρ h e)).add_mem ihx ihy
    | smul a x hx ih =>
      simpa using (Submodule.span ℂ (Set.range fun h => ρ h e)).smul_mem a ih

lemma self_mem_cyclic (ρ : Representation ℂ G E) (e : E) : e ∈ cyclic ρ e := by
  exact Submodule.subset_span ⟨1, by simp⟩


variable [contextInstance32_9 : FiniteDimensional ℂ E]

lemma starProjection_rep (ρ : Representation ℂ G E)
    (hunit : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (U : Subrepresentation ρ) (g : G) (v : E) :
    U.toSubmodule.starProjection (ρ g v) = ρ g (U.toSubmodule.starProjection v) := by
  apply U.toSubmodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact U.apply_mem_toSubmodule g (U.toSubmodule.starProjection_apply_mem v)
  · intro w hw
    have hw' := U.apply_mem_toSubmodule g⁻¹ hw
    have he : ρ g (ρ g⁻¹ w) = w := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [← map_sub]
    conv_lhs => rhs; rw [← he]
    rw [hunit]
    exact U.toSubmodule.starProjection_inner_eq_zero v _ hw'




theorem simple_eigen_submodule_alternative (ρ : Representation ℂ G E) (e : E)
    (hunit : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (g₀ : G) (c : ℂ) (heig : ρ g₀ e = c • e)
    (hsimple : ∀ v : E, ρ g₀ v = c • v → v ∈ Submodule.span ℂ {e})
    (U : Subrepresentation ρ) :
    cyclic ρ e ≤ U ∨ ∀ u ∈ U, ∀ v ∈ cyclic ρ e, ⟪v, u⟫_ℂ = 0 := by
  classical
  by_cases he : e ∈ U
  · left
    exact Submodule.span_le.mpr (by rintro _ ⟨g, rfl⟩; exact U.apply_mem_toSubmodule g he)
  · right
    have hp : U.toSubmodule.starProjection e = 0 := by
      have hpeig : ρ g₀ (U.toSubmodule.starProjection e) =
          c • U.toSubmodule.starProjection e := by
        rw [← starProjection_rep ρ hunit U g₀ e, heig, map_smul]
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hsimple _ hpeig)
      by_cases ha0 : a = 0
      · simpa [ha0] using ha.symm
      · apply False.elim
        apply he
        have hm := U.toSubmodule.starProjection_apply_mem e
        rw [← ha] at hm
        have hh := U.toSubmodule.smul_mem a⁻¹ hm
        change e ∈ U.toSubmodule
        simpa [smul_smul, ha0] using hh
    have heorth (u : E) (hu : u ∈ U) : ⟪e, u⟫_ℂ = 0 := by
      have hh := U.toSubmodule.starProjection_inner_eq_zero e u hu
      simpa [hp] using hh
    intro u hu v hv
    have horth (g : G) : ⟪ρ g e, u⟫_ℂ = 0 := by
      have hgu : ρ g⁻¹ u ∈ U := U.apply_mem_toSubmodule g⁻¹ hu
      have hi := hunit g e (ρ g⁻¹ u)
      simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply] using hi.trans (heorth _ hgu)
    induction hv using Submodule.span_induction with
    | mem v hv => obtain ⟨g, rfl⟩ := hv; exact horth g
    | zero => simp
    | add x y hx hy ihx ihy => simp [ihx, ihy]
    | smul a x hx ih => simp [ih]

theorem cyclic_irreducible_of_simple_eigen (ρ : Representation ℂ G E) (e : E) (he : e ≠ 0)
    (hunit : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (g₀ : G) (c : ℂ) (heig : ρ g₀ e = c • e)
    (hsimple : ∀ v : E, ρ g₀ v = c • v → v ∈ Submodule.span ℂ {e}) :
    Representation.IsIrreducible (cyclic ρ e).toRepresentation := by
  let S := cyclic ρ e
  let eS : S.toSubmodule := ⟨e, self_mem_cyclic ρ e⟩
  have heS : eS ≠ 0 := by intro hh; apply he; exact congrArg Subtype.val hh
  have htb : (⊤ : Subrepresentation S.toRepresentation) ≠ ⊥ := by
    intro hh
    have hel : eS ∈ (⊤ : Subrepresentation S.toRepresentation) := by trivial
    rw [hh] at hel
    exact heS hel
  let : Nontrivial (Subrepresentation S.toRepresentation) := ⟨⟨⊤, ⊥, htb⟩⟩
  refine ⟨fun U => ?_⟩
  let U' : Subrepresentation ρ := {
    toSubmodule := U.toSubmodule.map S.toSubmodule.subtype
    apply_mem_toSubmodule := by
      intro g v hv
      obtain ⟨u, hu, rfl⟩ := hv
      exact ⟨S.toRepresentation g u, U.apply_mem_toSubmodule g hu, rfl⟩ }
  rcases simple_eigen_submodule_alternative ρ e hunit g₀ c heig hsimple U' with h | h
  · right
    apply top_unique
    intro u _
    obtain ⟨v, hv, heq⟩ := h u.property
    have hvu : v = u := Subtype.ext heq
    exact hvu ▸ hv
  · left
    apply bot_unique
    intro u hu
    have hum : (u : E) ∈ U' := ⟨u, hu, rfl⟩
    have hh := h _ hum _ u.property
    have hz : (u : E) = 0 := inner_self_eq_zero.mp hh
    exact Subtype.ext hz
end SpinAngle.Specht




noncomputable section
open scoped BigOperators ComplexConjugate InnerProductSpace Matrix
namespace SpinAngle.TensorRep
variable {ι n : Type*} [contextInstance135_23 : Fintype ι] [contextInstance135_35 : DecidableEq ι] [contextInstance135_51 : Fintype n] [contextInstance135_63 : DecidableEq n]


def tensor (a : ι → Matrix n n ℂ) : Matrix (ι → n) (ι → n) ℂ :=
  fun x y => ∏ i, a i (x i) (y i)

lemma tensor_star
    {ι : Type*} {n : Type*}
    [contextInstance135_23 : Fintype ι]
    [DecidableEq ι]
    [Fintype n]
    [DecidableEq n] (a : ι → Matrix n n ℂ) :
    tensor (fun i => star (a i)) = star (tensor a) := by
  ext x y
  simp [tensor, Matrix.star_apply]

lemma tensor_mul
    {ι : Type*} {n : Type*}
    [contextInstance135_23 : Fintype ι]
    [contextInstance135_35 : DecidableEq ι]
    [contextInstance135_51 : Fintype n]
    [DecidableEq n] (a b : ι → Matrix n n ℂ) :
    tensor (fun i => a i * b i) = tensor a * tensor b := by
  ext x y
  simp only [tensor, Matrix.mul_apply, ← Finset.prod_mul_distrib]
  symm
  simpa using (Finset.sum_prod_piFinset (ι := ι) Finset.univ
    (fun i j => a i (x i) j * b i j (y i)))

lemma tensor_one
    {ι : Type*} {n : Type*}
    [contextInstance135_23 : Fintype ι]
    [DecidableEq ι]
    [Fintype n]
    [contextInstance135_63 : DecidableEq n] : tensor (fun _ : ι => (1 : Matrix n n ℂ)) = 1 := by
  ext x y
  classical
  by_cases h : x = y
  · subst y
    simp [tensor]
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    simp only [tensor, Matrix.one_apply, ite_eq_right h]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

lemma tensor_diagonal
    {ι : Type*} {n : Type*}
    [contextInstance135_23 : Fintype ι]
    [DecidableEq ι]
    [Fintype n]
    [contextInstance135_63 : DecidableEq n] (a : ι → n → ℂ) :
    tensor (fun i => Matrix.diagonal (a i)) = Matrix.diagonal (fun x => ∏ i, a i (x i)) := by
  ext x y
  classical
  by_cases h : x = y
  · subst y
    simp [tensor]
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    simp only [tensor, Matrix.diagonal_apply, ite_eq_right h]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

lemma toEuclideanLin_mul
    {ι : Type*} {n : Type*}
    [Fintype ι]
    [DecidableEq ι]
    [contextInstance135_51 : Fintype n]
    [contextInstance135_63 : DecidableEq n] (a b : Matrix n n ℂ) :
    Matrix.toEuclideanLin (a * b) =
      Matrix.toEuclideanLin a * Matrix.toEuclideanLin b := by
  ext v x
  change ((a * b) *ᵥ (WithLp.ofLp v)) x = (a *ᵥ (b *ᵥ (WithLp.ofLp v))) x
  rw [Matrix.mulVec_mulVec]

lemma toEuclideanLin_one
    {ι : Type*} {n : Type*}
    [Fintype ι]
    [DecidableEq ι]
    [contextInstance135_51 : Fintype n]
    [contextInstance135_63 : DecidableEq n] : Matrix.toEuclideanLin (1 : Matrix n n ℂ) = 1 := by
  ext v x
  change ((1 : Matrix n n ℂ) *ᵥ (WithLp.ofLp v)) x = v x
  simp


def action : Matrix n n ℂ →* Module.End ℂ (EuclideanSpace ℂ (ι → n)) where
  toFun a := Matrix.toEuclideanLin (tensor (fun _ : ι => a))
  map_one' := by rw [tensor_one, toEuclideanLin_one (ι := ι)]
  map_mul' a b := by rw [tensor_mul, toEuclideanLin_mul (ι := ι)]



def rep : Representation ℂ (Matrix.unitaryGroup n ℂ) (EuclideanSpace ℂ (ι → n)) :=
  action.comp (Matrix.unitaryGroup n ℂ).subtype

lemma tensor_mem_unitary (a : ι → Matrix.unitaryGroup n ℂ) :
    tensor (fun i => (a i : Matrix n n ℂ)) ∈ Matrix.unitaryGroup (ι → n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', ← tensor_star, ← tensor_mul]
  convert tensor_one (ι := ι) (n := n) using 1
  congr 1
  funext i
  exact (a i).property.1

lemma toEuclideanLin_unitary (a : Matrix n n ℂ) (ha : a ∈ Matrix.unitaryGroup n ℂ)
    (v w : EuclideanSpace ℂ n) :
    ⟪Matrix.toEuclideanLin a v, Matrix.toEuclideanLin a w⟫_ℂ = ⟪v, w⟫_ℂ := by
  rw [← LinearMap.adjoint_inner_right]
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  change ⟪v, (Matrix.toEuclideanLin (star a) * Matrix.toEuclideanLin a) w⟫_ℂ = _
  rw [← toEuclideanLin_mul (ι := n), ha.1, toEuclideanLin_one (ι := n)]
  rfl

lemma rep_unitary (g : Matrix.unitaryGroup n ℂ)
    (v w : EuclideanSpace ℂ (ι → n)) : ⟪rep g v, rep g w⟫_ℂ = ⟪v, w⟫_ℂ :=
  toEuclideanLin_unitary _ (tensor_mem_unitary (fun _ : ι => g)) v w


lemma tensor_reindex
    {ι : Type*} {n : Type*}
    [contextInstance135_23 : Fintype ι]
    [DecidableEq ι]
    [Fintype n]
    [DecidableEq n] (a : Matrix n n ℂ) (σ : Equiv.Perm ι) (x y : ι → n) :
    tensor (fun _ : ι => a) (x ∘ σ) (y ∘ σ) = tensor (fun _ : ι => a) x y := by
  exact Equiv.prod_comp σ (fun i => a (x i) (y i))


lemma action_diagonal (a : n → ℂ) (v : EuclideanSpace ℂ (ι → n)) (x : ι → n) :
    action (Matrix.diagonal a) v x = (∏ i, a (x i)) * v x := by
  change (Matrix.toEuclideanLin (tensor (fun _ : ι => Matrix.diagonal a)) v) x = _
  rw [tensor_diagonal]
  change (Matrix.diagonal (fun x : ι → n => ∏ i, a (x i)) *ᵥ WithLp.ofLp v) x = _
  exact Matrix.mulVec_diagonal _ _ _

end SpinAngle.TensorRep

namespace SpinAngle.Specht
open scoped Classical
variable {G : Type*} [contextInstance243_21 : Group G]
namespace PermutationSpace
open scoped Classical

variable {X : Type*} [contextInstance247_21 : Fintype X] [contextInstance247_33 : MulAction G X]


def rep : Representation ℂ G (EuclideanSpace ℂ X) where
  toFun g := {
    toFun v := WithLp.toLp 2 (fun x => v (g⁻¹ • x))
    map_add' := by intro v w; rfl
    map_smul' := by intro a v; rfl }
  map_one' := by ext v x; simp
  map_mul' := by
    intro g h
    ext v x
    change v ((g * h)⁻¹ • x) = v (h⁻¹ • g⁻¹ • x)
    simp [mul_smul]

omit [Fintype X] in
@[simp] lemma rep_apply (g : G) (v : EuclideanSpace ℂ X) (x : X) :
    rep g v x = v (g⁻¹ • x) := rfl

lemma rep_unitary (g : G) (v w : EuclideanSpace ℂ X) :
    ⟪rep g v, rep g w⟫_ℂ = ⟪v, w⟫_ℂ := by
  simp only [PiLp.inner_apply, rep_apply]
  exact Equiv.sum_comp (MulAction.toPerm g⁻¹) (fun x => inner ℂ (v x) (w x))

omit [Fintype X] in
lemma rep_single (g : G) (x : X) :
    rep g (EuclideanSpace.single x (1 : ℂ)) = EuclideanSpace.single (g • x) (1 : ℂ) := by
  classical
  ext y
  simp only [rep_apply, PiLp.single_apply, inv_smul_eq_iff]

variable {H : Type*} [contextInstance278_21 : Group H] [contextInstance278_31 : Fintype H]



def alternator (ι : H →* G) (χ : H →* ℂ) : Module.End ℂ (EuclideanSpace ℂ X) :=
  ∑ h, χ h • rep (ι h)

omit [Fintype X] in
lemma alternator_apply (ι : H →* G) (χ : H →* ℂ) (v : EuclideanSpace ℂ X) :
    alternator ι χ v = ∑ h, χ h • rep (ι h) v := by
  simp [alternator, LinearMap.sum_apply]

omit [Fintype X] in
lemma alternator_stable (ι : H →* G) (χ : H →* ℂ)
    (U : Subrepresentation (rep : Representation ℂ G (EuclideanSpace ℂ X)))
    (v : EuclideanSpace ℂ X) (hv : v ∈ U) : alternator ι χ v ∈ U := by
  rw [alternator_apply]
  exact U.toSubmodule.sum_mem fun h _ => U.toSubmodule.smul_mem _ (U.apply_mem_toSubmodule _ hv)

omit [Fintype X] in
lemma alternator_translate (ι : H →* G) (χ : H →* ℂ) (a : H)
    (v : EuclideanSpace ℂ X) :
    alternator ι χ (rep (ι a) v) = χ a⁻¹ • alternator ι χ v := by
  rw [alternator_apply, alternator_apply, Finset.smul_sum]
  have he := Equiv.sum_comp (Equiv.mulRight a)
    (fun h => χ a⁻¹ • (χ h • (rep (ι h) v : EuclideanSpace ℂ X)))
  rw [← he]
  apply Finset.sum_congr rfl
  intro h _
  simp only [Equiv.coe_mulRight, smul_smul, map_mul]
  rw [show χ a⁻¹ * (χ h * χ a) = χ h by
    calc
      _ = χ h * (χ a⁻¹ * χ a) := by ring
      _ = χ h := by rw [← map_mul, inv_mul_cancel, map_one, mul_one]]
  simp only [Module.End.mul_apply]

omit [Fintype X] in
lemma alternator_single_zero (ι : H →* G) (χ : H →* ℂ)
    (x : X) (a : H) (ha : ι a • x = x) (hs : χ a = -1) :
    alternator ι χ (EuclideanSpace.single x (1 : ℂ)) = 0 := by
  have hh := alternator_translate ι χ a (EuclideanSpace.single x (1 : ℂ))
  rw [rep_single, ha, map_inv, hs, inv_neg, inv_one, neg_smul, one_smul] at hh
  have hz := congrArg (fun z => z + alternator ι χ (EuclideanSpace.single x (1 : ℂ))) hh
  have ht : (2 : ℂ) • alternator ι χ (EuclideanSpace.single x (1 : ℂ)) = 0 := by
    simpa [two_smul] using hz
  exact (smul_eq_zero.mp ht).resolve_left (by norm_num)

omit [Fintype X] in
lemma alternator_coeff (ι : H →* G) (χ : H →* ℂ) (v : EuclideanSpace ℂ X) (x : X) :
    alternator ι χ v x = ∑ h, χ h * v ((ι h)⁻¹ • x) := by
  simp [alternator_apply, WithLp.ofLp_sum, Finset.sum_apply]

omit [Fintype X] in
lemma polytabloid_base [DecidableEq X] (ι : H →* G) (χ : H →* ℂ) (b : X)
    (hfree : ∀ h : H, ι h • b = b → h = 1) :
    alternator ι χ (EuclideanSpace.single b (1 : ℂ)) b = 1 := by
  classical
  rw [alternator_coeff, Finset.sum_eq_single 1]
  · simp
  · intro h _ hh
    have hn : (ι h)⁻¹ • b ≠ b := by
      intro he
      have hi : h⁻¹ = 1 := hfree h⁻¹ (by simpa using he)
      exact hh (inv_eq_one.mp hi)
    simp [hn]
  · simp

lemma polytabloid_inner (ι : H →* G) (χ : H →* ℂ) (b : X)
    (hreal : ∀ h, conj (χ h) = χ h) (hinv : ∀ h, χ h⁻¹ = χ h)
    (v : EuclideanSpace ℂ X) :
    ⟪alternator ι χ (EuclideanSpace.single b (1 : ℂ)), v⟫_ℂ = alternator ι χ v b := by
  classical
  rw [alternator_apply, sum_inner, alternator_coeff]
  simp only [inner_smul_left, rep_single, EuclideanSpace.inner_single_left, map_one,
    one_mul, hreal]
  have hh := Equiv.sum_comp (Equiv.inv H) (fun h => χ h * v ((ι h)⁻¹ • b))
  simpa only [Equiv.inv_apply, map_inv, inv_inv, hinv] using hh



theorem alternator_rank_one (ι : H →* G) (χ : H →* ℂ) (b : X)
    (hreal : ∀ h, conj (χ h) = χ h) (hinv : ∀ h, χ h⁻¹ = χ h)
    (hfree : ∀ h : H, ι h • b = b → h = 1)
    (halt : ∀ x : X, (∃ a : H, ι a • x = x ∧ χ a = -1) ∨
      ∃ a : H, x = ι a • b) (v : EuclideanSpace ℂ X) :
    alternator ι χ v =
      ⟪alternator ι χ (EuclideanSpace.single b (1 : ℂ)), v⟫_ℂ •
        alternator ι χ (EuclideanSpace.single b (1 : ℂ)) := by
  classical
  let e := alternator ι χ (EuclideanSpace.single b (1 : ℂ))
  have hs (x : X) : alternator ι χ (EuclideanSpace.single x (1 : ℂ)) ∈ Submodule.span ℂ {e} := by
    rcases halt x with ⟨a, ha, hχ⟩ | ⟨a, rfl⟩
    · rw [alternator_single_zero ι χ x a ha hχ]
      exact Submodule.zero_mem _
    · rw [← rep_single, alternator_translate]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton e))
  have hv : alternator ι χ v ∈ Submodule.span ℂ {e} := by
    have hexp := (EuclideanSpace.basisFun X ℂ).sum_repr v
    simp only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] at hexp
    rw [← hexp, map_sum]
    exact Submodule.sum_mem _ fun x _ => by
      rw [map_smul]
      exact Submodule.smul_mem _ _ (hs x)
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hv
  have heb : e b = 1 := polytabloid_base ι χ b hfree
  have hab : a = alternator ι χ v b := by
    have hh := congrArg (fun z : EuclideanSpace ℂ X => z b) ha
    simpa only [PiLp.smul_apply, smul_eq_mul, heb, mul_one] using hh
  rw [← ha, hab, polytabloid_inner ι χ b hreal hinv]

end PermutationSpace
variable {α : Type*} [contextInstance389_21 : Fintype α]

def complexSign : Equiv.Perm α →* ℂ where
  toFun g := ((Equiv.Perm.sign g : ℤˣ) : ℤ)
  map_one' := by simp
  map_mul' := by intro g h; simp

@[simp] lemma complexSign_conj (g : Equiv.Perm α) : conj (complexSign g) = complexSign g := by
  simp [complexSign]

@[simp] lemma complexSign_inv (g : Equiv.Perm α) : complexSign g⁻¹ = complexSign g := by
  simp [complexSign]

@[simp] lemma complexSign_swap (x y : α) (h : x ≠ y) : complexSign (Equiv.swap x y) = -1 := by
  simp [complexSign, Equiv.Perm.sign_swap h]


end SpinAngle.Specht

namespace SpinAngle.Young

abbrev Cells (D : YoungDiagram) := {p : ℕ × ℕ // p ∈ D.cells}

lemma fin_le_strictMono {n : ℕ} (f : Fin n → ℕ) (hf : StrictMono f) (i : Fin n) :
    i.val ≤ f i := by
  have aux : ∀ k (hk : k < n), k ≤ f ⟨k, hk⟩ := by
    intro k
    induction k with
    | zero => intro hk; exact Nat.zero_le _
    | succ k ih =>
      intro hk
      have hk' : k < n := by omega
      have hl := hf (show (⟨k, hk'⟩ : Fin n) < ⟨k + 1, hk⟩ from by simp)
      have hi := ih hk'
      omega
  exact aux i.val i.isLt

lemma card_column (D : YoungDiagram) (j : ℕ) :
    (Finset.univ.filter fun x : Cells D => x.val.2 = j).card = D.colLen j := by
  classical
  let e : {x : Cells D // x.val.2 = j} ≃ Fin (D.colLen j) := {
    toFun := fun x => ⟨x.val.val.1, YoungDiagram.mem_iff_lt_colLen.mp (by
      have hx : (x.val.val.1, x.val.val.2) ∈ D := x.val.property
      simpa only [x.property] using hx)⟩
    invFun := fun i => ⟨⟨(i, j), YoungDiagram.mem_iff_lt_colLen.mpr i.isLt⟩, rfl⟩
    left_inv := by intro x; apply Subtype.ext; apply Subtype.ext; exact Prod.ext rfl x.property.symm
    right_inv := by intro i; rfl }
  rw [← Fintype.card_subtype]
  exact (Fintype.card_congr e).trans (Fintype.card_fin _)

lemma card_row_subtype (D : YoungDiagram) (i : ℕ) :
    Fintype.card {x : Cells D // x.val.1 = i} = D.rowLen i := by
  let e : {x : Cells D // x.val.1 = i} ≃ Fin (D.rowLen i) := {
    toFun := fun x => ⟨x.val.val.2, YoungDiagram.mem_iff_lt_rowLen.mp (by
      have hx : (x.val.val.1, x.val.val.2) ∈ D := x.val.property
      simpa only [x.property] using hx)⟩
    invFun := fun j => ⟨⟨(i, j), YoungDiagram.mem_iff_lt_rowLen.mpr j.isLt⟩, rfl⟩
    left_inv := by intro x; apply Subtype.ext; apply Subtype.ext; exact Prod.ext x.property.symm rfl
    right_inv := by intro j; rfl }
  exact (Fintype.card_congr e).trans (Fintype.card_fin _)

lemma eq_of_rowPreserving (D E : YoungDiagram) (e : Cells D ≃ Cells E)
    (he : ∀ x, (e x).val.1 = x.val.1) : D = E := by
  have hr (i : ℕ) : D.rowLen i = E.rowLen i := by
    rw [← card_row_subtype D i, ← card_row_subtype E i]
    exact Fintype.card_congr (e.subtypeEquiv (fun x => by rw [he]))
  apply YoungDiagram.ext
  ext p
  obtain ⟨i, j⟩ := p
  change (i, j) ∈ D ↔ (i, j) ∈ E
  simp only [YoungDiagram.mem_iff_lt_rowLen, hr]




theorem column_sort_le (D : YoungDiagram) (r : Cells D → ℕ)
    (hinj : ∀ x y : Cells D, x.val.2 = y.val.2 → r x = r y → x = y)
    :
    ∃ σ : Equiv.Perm (Cells D), (∀ x, (σ x).val.2 = x.val.2) ∧
      ∀ x, x.val.1 ≤ r (σ x) := by
  classical
  let S (j : ℕ) : Finset ℕ := (Finset.univ.filter fun x : Cells D => x.val.2 = j).image r
  have hc (j : ℕ) : (S j).card = D.colLen j := by
    change ((Finset.univ.filter fun x : Cells D => x.val.2 = j).image r).card = _
    rw [Finset.card_image_iff.mpr (show Set.InjOn r ↑(Finset.univ.filter fun x : Cells D => x.val.2 = j) from by
      intro x hx y hy hxy
      exact hinj x y ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm) hxy)]
    exact card_column D j
  let F (j : ℕ) := (S j).orderEmbOfFin (hc j)
  have hpre (x : Cells D) : ∃ y : Cells D, y.val.2 = x.val.2 ∧
      r y = F x.val.2 ⟨x.val.1, YoungDiagram.mem_iff_lt_colLen.mp x.property⟩ := by
    have hm := (S x.val.2).orderEmbOfFin_mem (hc _) ⟨x.val.1, YoungDiagram.mem_iff_lt_colLen.mp x.property⟩
    obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hm
    exact ⟨y, (Finset.mem_filter.mp hy).2, he⟩
  choose f hcol hr using hpre
  have hf : Function.Injective f := by
    intro x y he
    have hj : x.val.2 = y.val.2 := (hcol x).symm.trans ((congrArg (fun z : Cells D => z.val.2) he).trans (hcol y))
    have hi : x.val.1 = y.val.1 := by
      have hval : F x.val.2 ⟨x.val.1, YoungDiagram.mem_iff_lt_colLen.mp x.property⟩ =
          F y.val.2 ⟨y.val.1, YoungDiagram.mem_iff_lt_colLen.mp y.property⟩ := by
        rw [← hr x, ← hr y, he]
      have hy : y.val.1 < D.colLen x.val.2 := by rw [hj]; exact YoungDiagram.mem_iff_lt_colLen.mp y.property
      have hid : F y.val.2 ⟨y.val.1, YoungDiagram.mem_iff_lt_colLen.mp y.property⟩ = F x.val.2 ⟨y.val.1, hy⟩ := by
        have aux (j k i : ℕ) (hk : j = k) (hi : i < D.colLen j) (hi' : i < D.colLen k) :
            F j ⟨i, hi⟩ = F k ⟨i, hi'⟩ := by subst k; rfl
        exact aux _ _ _ hj.symm _ _
      rw [hid] at hval
      exact congrArg Fin.val ((F x.val.2).injective hval)
    exact Subtype.ext (Prod.ext hi hj)
  let σ : Equiv.Perm (Cells D) := Equiv.ofBijective f ⟨hf, Finite.surjective_of_injective hf⟩
  refine ⟨σ, hcol, ?_⟩
  have hle (x : Cells D) : x.val.1 ≤ r (σ x) := by
    change x.val.1 ≤ r (f x)
    rw [hr]
    exact fin_le_strictMono _ (F x.val.2).strictMono ⟨x.val.1, YoungDiagram.mem_iff_lt_colLen.mp x.property⟩
  exact hle

lemma rowRankSum_le (D : YoungDiagram) (r : Cells D → ℕ)
    (hinj : ∀ x y : Cells D, x.val.2 = y.val.2 → r x = r y → x = y) :
    ∑ x : Cells D, x.val.1 ≤ ∑ x : Cells D, r x := by
  obtain ⟨σ, -, hσ⟩ := column_sort_le D r hinj
  rw [← Equiv.sum_comp σ r]
  exact Finset.sum_le_sum fun x _ => hσ x

theorem column_sort (D : YoungDiagram) (r : Cells D → ℕ)
    (hinj : ∀ x y : Cells D, x.val.2 = y.val.2 → r x = r y → x = y)
    (hsum : ∑ x : Cells D, r x = ∑ x : Cells D, x.val.1) :
    ∃ σ : Equiv.Perm (Cells D), (∀ x, (σ x).val.2 = x.val.2) ∧
      ∀ x, r (σ x) = x.val.1 := by
  obtain ⟨σ, hc, hle⟩ := column_sort_le D r hinj
  refine ⟨σ, hc, ?_⟩
  have heq : ∑ x : Cells D, x.val.1 = ∑ x : Cells D, r (σ x) := by
    rw [Equiv.sum_comp σ r, hsum]
  have hh := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (fun x _ => hle x)).mp heq
  intro x
  exact (hh x (Finset.mem_univ x)).symm

end SpinAngle.Young

namespace SpinAngle.PolynomialCarrier
open scoped Classical Matrix
open SpinAngle.Specht SpinAngle.Young
variable {ι n : Type*} [contextInstance532_23 : Fintype ι] [contextInstance532_35 : DecidableEq ι] [contextInstance532_51 : Fintype n] [contextInstance532_63 : DecidableEq n]


instance coloringAction : MulAction (Equiv.Perm ι) (ι → n) where
  smul g x := x ∘ g.symm
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

lemma site_apply
    {ι : Type*} {n : Type*}
    [Fintype ι]
    [DecidableEq ι]
    [Fintype n]
    [DecidableEq n] (g : Equiv.Perm ι) (v : EuclideanSpace ℂ (ι → n)) (x : ι → n) :
    PermutationSpace.rep g v x = v (x ∘ g) := rfl

def reindex (g : Equiv.Perm ι) : (ι → n) ≃ (ι → n) where
  toFun x := x ∘ g
  invFun x := x ∘ g.symm
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp

lemma action_site_commute (a : Matrix n n ℂ) (g : Equiv.Perm ι)
    (v : EuclideanSpace ℂ (ι → n)) :
    TensorRep.action a (PermutationSpace.rep g v) =
      PermutationSpace.rep g (TensorRep.action a v) := by
  ext x
  change (∑ y, TensorRep.tensor (fun _ : ι => a) x y * v (y ∘ g)) =
    ∑ y, TensorRep.tensor (fun _ : ι => a) (x ∘ g) y * v y
  rw [← Equiv.sum_comp (reindex (n := n) g)
    (fun y => TensorRep.tensor (fun _ : ι => a) (x ∘ g) y * v y)]
  apply Finset.sum_congr rfl
  intro y _
  change _ = TensorRep.tensor (fun _ : ι => a) (x ∘ g) (y ∘ g) * v (y ∘ g)
  rw [TensorRep.tensor_reindex]


def columnGroup (D : YoungDiagram) : Subgroup (Equiv.Perm (Cells D)) where
  carrier := {g | ∀ x, (g x).val.2 = x.val.2}
  one_mem' := fun _ => rfl
  mul_mem' := by intro g h hg hh x; exact (hg (h x)).trans (hh x)
  inv_mem' := by
    intro g hg x
    simpa using (hg (g⁻¹ x)).symm

variable (D : YoungDiagram) (q : ℕ)
abbrev TensorSpace := EuclideanSpace ℂ (Cells D → Fin q)



def alternating : Subrepresentation (TensorRep.rep (ι := Cells D) (n := Fin q)) where
  toSubmodule := {
    carrier := {v | ∀ g : columnGroup D,
      PermutationSpace.rep (g : Equiv.Perm (Cells D)) v = complexSign g.val • v}
    zero_mem' := by intro g; simp
    add_mem' := by intro x y hx hy g; simp [map_add, hx g, hy g, smul_add]
    smul_mem' := by intro c x hx g; simp [map_smul, hx g, smul_comm c] }
  apply_mem_toSubmodule a := by
    intro v hv g
    change PermutationSpace.rep g.val (TensorRep.action (a : Matrix (Fin q) (Fin q) ℂ) v) = _
    rw [← action_site_commute, hv g, map_smul]
    rfl

variable (hq : D.colLen 0 ≤ q)

def rowColor : Cells D → Fin q := fun x => ⟨x.val.1, by
  have hm := D.up_left_mem le_rfl (Nat.zero_le x.val.2) x.property
  have hl := YoungDiagram.mem_iff_lt_colLen.mp hm
  exact lt_of_lt_of_le hl hq⟩

def highest : TensorSpace D q := by
  classical
  exact PermutationSpace.alternator (columnGroup D).subtype
    (complexSign.comp (columnGroup D).subtype)
    (EuclideanSpace.single (rowColor D q hq) (1 : ℂ))

lemma rowColor_column_free
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (D : YoungDiagram) (q : ℕ) (hq : D.colLen 0 ≤ q) (g : columnGroup D)
    (hg : g.val • rowColor D q hq = rowColor D q hq) : g = 1 := by
  apply Subtype.ext
  apply Equiv.Perm.ext
  intro x
  apply Subtype.ext
  apply Prod.ext
  · have hh := congrFun hg (g.val x)
    have hh' := congrArg Fin.val hh
    change (g.val x).val.1 = x.val.1
    change ((g.val x |> g.val.symm)).val.1 = (g.val x).val.1 at hh'
    simp only [Equiv.symm_apply_apply] at hh'
    exact hh'.symm
  · exact g.property x

lemma highest_base : highest D q hq (rowColor D q hq) = 1 := by
  classical
  unfold highest
  exact PermutationSpace.polytabloid_base (columnGroup D).subtype
    (complexSign.comp (columnGroup D).subtype) (rowColor D q hq)
    (rowColor_column_free (ι := Cells D) D q hq)

lemma highest_ne_zero : highest D q hq ≠ 0 := by
  intro he
  have hh := congrArg (fun v : TensorSpace D q => v (rowColor D q hq)) he
  simp [highest_base] at hh

end SpinAngle.PolynomialCarrier

namespace SpinAngle.Specht.PermutationSpace
open scoped Classical
variable {G H X : Type*} [contextInstance635_25 : Group G] [contextInstance635_35 : Group H] [contextInstance635_45 : Fintype H] [contextInstance635_57 : Fintype X] [contextInstance635_69 : MulAction G X]
lemma rep_alternator
    {G : Type*} {H : Type*} {X : Type*}
    [contextInstance635_25 : Group G]
    [contextInstance635_35 : Group H]
    [contextInstance635_45 : Fintype H]
    [Fintype X]
    [contextInstance635_69 : MulAction G X] (ι : H →* G) (χ : H →* ℂ) (a : H)
    (v : EuclideanSpace ℂ X) :
    rep (ι a) (alternator ι χ v) = χ a⁻¹ • alternator ι χ v := by
  rw [alternator_apply, map_sum, Finset.smul_sum]
  have he := Equiv.sum_comp (Equiv.mulLeft a)
    (fun h => χ a⁻¹ • (χ h • (rep (ι h) v : EuclideanSpace ℂ X)))
  rw [← he]
  apply Finset.sum_congr rfl
  intro h _
  simp only [Equiv.coe_mulLeft, smul_smul, map_mul, map_smul]
  rw [show χ a⁻¹ * (χ a * χ h) = χ h by
    rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]]
  rfl
end SpinAngle.Specht.PermutationSpace

namespace SpinAngle.PolynomialCarrier
open scoped Classical Matrix
open SpinAngle.Specht SpinAngle.Young
variable (D : YoungDiagram) (q : ℕ) (hq : D.colLen 0 ≤ q)

lemma highest_mem : highest D q hq ∈ alternating D q := by
  classical
  intro g
  change PermutationSpace.rep g.val (PermutationSpace.alternator _ _ _) = _
  have hh := PermutationSpace.rep_alternator (columnGroup D).subtype
    (complexSign.comp (columnGroup D).subtype) g (EuclideanSpace.single (rowColor D q hq) (1 : ℂ))
  change PermutationSpace.rep g.val (highest D q hq) = complexSign (g.val⁻¹) • highest D q hq at hh
  rw [complexSign_inv] at hh
  exact hh


lemma alternating_collision (v : TensorSpace D q) (hv : v ∈ alternating D q)
    (x : Cells D → Fin q) (i j : Cells D) (hij : i ≠ j)
    (hc : i.val.2 = j.val.2) (hx : x i = x j) : v x = 0 := by
  classical
  let : DecidableEq (Cells D) := Classical.decEq _
  let g : columnGroup D := ⟨Equiv.swap i j, by
    intro k
    by_cases hki : k = i
    · subst k; simp [hc]
    by_cases hkj : k = j
    · subst k; simp [hc]
    rw [Equiv.swap_apply_of_ne_of_ne hki hkj]⟩
  have hperm : x ∘ (g : Equiv.Perm (Cells D)) = x := by
    funext k
    change x (Equiv.swap i j k) = x k
    by_cases hki : k = i
    · subst k; simp [hx]
    by_cases hkj : k = j
    · subst k; simp [hx]
    rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
  have hh := congrArg (fun w : TensorSpace D q => w x) (hv g)
  simp only [site_apply, hperm, PiLp.smul_apply, smul_eq_mul] at hh
  have hg : complexSign g.val = -1 := by
    simpa only [g] using complexSign_swap i j hij
  rw [hg, neg_one_mul] at hh
  linear_combination (1/2 : ℂ) * hh

lemma alternating_injective (v : TensorSpace D q) (hv : v ∈ alternating D q)
    (x : Cells D → Fin q) (hx : v x ≠ 0) :
    ∀ i j : Cells D, i.val.2 = j.val.2 → (x i).val = (x j).val → i = j := by
  intro i j hc he
  by_contra hij
  exact hx (alternating_collision D q v hv x i j hij hc (Fin.ext he))



lemma alternating_minimal_weight (v : TensorSpace D q) (hv : v ∈ alternating D q)
    (x : Cells D → Fin q) (hw : ∑ i, (x i).val = ∑ i : Cells D, i.val.1) :
    v x = v (rowColor D q hq) * highest D q hq x := by
  by_cases hx : v x = 0
  · by_cases he : highest D q hq x = 0
    · rw [hx, he, mul_zero]
    · obtain ⟨σ, hc, hr⟩ := column_sort D (fun i => (x i).val)
        (alternating_injective D q (highest D q hq) (highest_mem D q hq) x he) hw
      let g : columnGroup D := ⟨σ, hc⟩
      have hcolor : x ∘ σ = rowColor D q hq := by funext i; exact Fin.ext (hr i)
      have hh := congrArg (fun w : TensorSpace D q => w x) (hv g)
      simp only [site_apply, PiLp.smul_apply, smul_eq_mul] at hh
      change v (x ∘ σ) = complexSign σ * v x at hh
      rw [hcolor, hx, mul_zero] at hh
      rw [hx, hh, zero_mul]
  · obtain ⟨σ, hc, hr⟩ := column_sort D (fun i => (x i).val)
      (alternating_injective D q v hv x hx) hw
    let g : columnGroup D := ⟨σ, hc⟩
    have hcolor : x ∘ σ = rowColor D q hq := by funext i; exact Fin.ext (hr i)
    have hh := congrArg (fun w : TensorSpace D q => w x) (hv g)
    have he := congrArg (fun w : TensorSpace D q => w x) (highest_mem D q hq g)
    simp only [site_apply, PiLp.smul_apply, smul_eq_mul] at hh he
    change v (x ∘ σ) = complexSign σ * v x at hh
    change highest D q hq (x ∘ σ) = complexSign σ * highest D q hq x at he
    rw [hcolor] at hh he
    rw [highest_base] at he
    rw [hh]
    calc
      v x = v x * 1 := (mul_one _).symm
      _ = v x * (complexSign σ * highest D q hq x) := by rw [← he]
      _ = complexSign σ * v x * highest D q hq x := by ring

end SpinAngle.PolynomialCarrier

namespace SpinAngle.PolynomialCarrier
open scoped Classical Matrix
open SpinAngle.Specht SpinAngle.Young
variable {ι : Type*} [contextInstance741_21 : Fintype ι] [contextInstance741_33 : DecidableEq ι] {q : ℕ}

lemma diagonal_single (a : Fin q → ℂ) (b : ι → Fin q) :
    TensorRep.action (Matrix.diagonal a) (EuclideanSpace.single b (1 : ℂ)) =
      (∏ i, a (b i)) • EuclideanSpace.single b (1 : ℂ) := by
  ext x
  rw [TensorRep.action_diagonal]
  simp only [PiLp.smul_apply, smul_eq_mul, PiLp.single_apply]
  by_cases h : x = b
  · subst x; rfl
  · simp [h]

lemma diagonal_unitary {z : ℂ} (hz : star z * z = 1) :
    Matrix.diagonal (fun i : Fin q => z ^ i.val) ∈ Matrix.unitaryGroup (Fin q) ℂ := by
  have hd : star (Matrix.diagonal (fun i : Fin q => z ^ i.val)) =
      Matrix.diagonal (fun i : Fin q => star (z ^ i.val)) := by
    ext i j
    by_cases h : i = j
    · subst j; simp [Matrix.star_apply]
    · simp [Matrix.star_apply, h, Ne.symm h]
  rw [Matrix.mem_unitaryGroup_iff', hd, Matrix.diagonal_mul_diagonal]
  simp only [star_pow, ← mul_pow, hz, one_pow]
  exact Matrix.diagonal_one

variable (D : YoungDiagram) (q : ℕ) (hq : D.colLen 0 ≤ q)

def weightOrder : ℕ := Fintype.card (Cells D) * q + 1

def weightRoot : ℂ := Complex.exp (2 * Real.pi * Complex.I / weightOrder D q)

lemma weightRoot_primitive : IsPrimitiveRoot (weightRoot D q) (weightOrder D q) :=
  Complex.isPrimitiveRoot_exp _ (by unfold weightOrder; omega)

lemma weightRoot_unitary : star (weightRoot D q) * weightRoot D q = 1 := by
  have hn := Complex.norm_eq_one_of_pow_eq_one
    (weightRoot_primitive D q).pow_eq_one (show weightOrder D q ≠ 0 by unfold weightOrder; omega)
  rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]
  norm_num

def weightElement : Matrix.unitaryGroup (Fin q) ℂ :=
  ⟨Matrix.diagonal (fun i => weightRoot D q ^ i.val), diagonal_unitary (weightRoot_unitary D q)⟩

lemma weight_sum_lt (x : Cells D → Fin q) : ∑ i, (x i).val < weightOrder D q := by
  have hh : (∑ i, (x i).val) ≤ ∑ _i : Cells D, q :=
    Finset.sum_le_sum fun i _ => (x i).isLt.le
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hh
  unfold weightOrder
  omega

lemma weight_action (v : TensorSpace D q) (x : Cells D → Fin q) :
    TensorRep.rep (weightElement D q) v x = weightRoot D q ^ (∑ i, (x i).val) * v x := by
  change TensorRep.action (Matrix.diagonal (fun i : Fin q => weightRoot D q ^ i.val)) v x = _
  rw [TensorRep.action_diagonal, Finset.prod_pow_eq_pow_sum]

lemma highest_diagonal (a : Fin q → ℂ) :
    TensorRep.action (Matrix.diagonal a) (highest D q hq) =
      (∏ i, a (rowColor D q hq i)) • highest D q hq := by
  unfold highest
  rw [PermutationSpace.alternator_apply, map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro g _
  rw [map_smul, action_site_commute, diagonal_single, map_smul]
  exact smul_comm _ _ _

lemma highest_weight_eigen :
    TensorRep.rep (weightElement D q) (highest D q hq) =
      weightRoot D q ^ (∑ i : Cells D, i.val.1) • highest D q hq := by
  change TensorRep.action (Matrix.diagonal _) _ = _
  rw [highest_diagonal]
  congr 1
  exact Finset.prod_pow_eq_pow_sum _ _ _

include hq in
lemma weight_eigen_support (v : TensorSpace D q)
    (hv : TensorRep.rep (weightElement D q) v =
      weightRoot D q ^ (∑ i : Cells D, i.val.1) • v)
    (x : Cells D → Fin q) (hx : v x ≠ 0) :
    ∑ i, (x i).val = ∑ i : Cells D, i.val.1 := by
  have hh := congrArg (fun w : TensorSpace D q => w x) hv
  rw [weight_action] at hh
  simp only [PiLp.smul_apply, smul_eq_mul] at hh
  have hp := mul_right_cancel₀ hx hh
  apply (weightRoot_primitive D q).pow_inj (weight_sum_lt D q x) _ hp
  exact weight_sum_lt D q (rowColor D q hq)


theorem weight_eigenspace_one_dimensional (v : TensorSpace D q)
    (hv : v ∈ alternating D q)
    (heig : TensorRep.rep (weightElement D q) v =
      weightRoot D q ^ (∑ i : Cells D, i.val.1) • v) :
    v = v (rowColor D q hq) • highest D q hq := by
  ext x
  change v x = v (rowColor D q hq) * highest D q hq x
  by_cases hw : ∑ i, (x i).val = ∑ i : Cells D, i.val.1
  · exact alternating_minimal_weight D q hq v hv x hw
  · have hv0 : v x = 0 := by
      by_contra hn
      exact hw (weight_eigen_support D q hq v heig x hn)
    have he0 : highest D q hq x = 0 := by
      by_contra hn
      exact hw (weight_eigen_support D q hq _ (highest_weight_eigen D q hq) x hn)
    rw [hv0, he0, mul_zero]



def ordinary : Subrepresentation (alternating D q).toRepresentation :=
  cyclic (alternating D q).toRepresentation
    (⟨highest D q hq, highest_mem D q hq⟩ : (alternating D q).toSubmodule)

theorem ordinary_irreducible : Representation.IsIrreducible (ordinary D q hq).toRepresentation := by
  refine cyclic_irreducible_of_simple_eigen _ _ ?_ ?_ (weightElement D q)
    (weightRoot D q ^ (∑ i : Cells D, i.val.1)) ?_ ?_
  · intro he
    exact highest_ne_zero D q hq (congrArg Subtype.val he)
  · intro g x y
    exact TensorRep.rep_unitary g (x : TensorSpace D q) (y : TensorSpace D q)
  · exact Subtype.ext (highest_weight_eigen D q hq)
  · intro v hv
    apply Submodule.mem_span_singleton.mpr
    refine ⟨v.val (rowColor D q hq), ?_⟩
    apply Subtype.ext
    exact (weight_eigenspace_one_dimensional D q hq v.val v.property (congrArg Subtype.val hv)).symm

end SpinAngle.PolynomialCarrier

namespace SpinAngle.TensorRep
open scoped Classical
variable {ι κ n : Type*} [contextInstance868_25 : Fintype ι] [contextInstance868_37 : DecidableEq ι] [contextInstance868_53 : Fintype κ] [contextInstance868_65 : DecidableEq κ]
  [contextInstance869_2 : Fintype n] [contextInstance869_14 : DecidableEq n]

lemma diagonal_unitary_of_star_mul (a : n → ℂ) (ha : ∀ i, star (a i) * a i = 1) :
    Matrix.diagonal a ∈ Matrix.unitaryGroup n ℂ := by
  have hd : star (Matrix.diagonal a) = Matrix.diagonal (fun i => star (a i)) := by
    ext i j
    by_cases h : i = j
    · subst j; simp [Matrix.star_apply]
    · simp [Matrix.star_apply, h, Ne.symm h]
  rw [Matrix.mem_unitaryGroup_iff', hd, Matrix.diagonal_mul_diagonal]
  simp only [ha]
  exact Matrix.diagonal_one

lemma diagonal_single [DecidableEq (ι → n)] (a : n → ℂ) (b : ι → n) :
    action (Matrix.diagonal a) (EuclideanSpace.single b (1 : ℂ)) =
      (∏ i, a (b i)) • EuclideanSpace.single b (1 : ℂ) := by
  ext x
  rw [action_diagonal]
  simp only [PiLp.smul_apply, smul_eq_mul, PiLp.single_apply]
  by_cases h : x = b
  · subst x; rfl
  · simp [h]

def content (x : ι → n) (j : n) : ℕ := (Finset.univ.filter fun i => x i = j).card

lemma product_content
    {ι : Type*} {n : Type*}
    [contextInstance868_25 : Fintype ι]
    [DecidableEq ι]
    [contextInstance869_2 : Fintype n]
    [contextInstance869_14 : DecidableEq n] (a : n → ℂ) (x : ι → n) :
    ∏ i, a (x i) = ∏ j, a j ^ content x j := by
  rw [← Finset.prod_fiberwise' Finset.univ x a]
  simp only [Finset.prod_const, content]

lemma phase_product
    {ι : Type*} {n : Type*}
    [contextInstance868_25 : Fintype ι]
    [DecidableEq ι]
    [Fintype n]
    [contextInstance869_14 : DecidableEq n] (z : ℂ) (j : n) (x : ι → n) :
    ∏ i, (if x i = j then z else 1) = z ^ content x j := by
  rw [← Finset.prod_filter]
  simp [content]

lemma content_le_card
    {ι : Type*} {n : Type*}
    [contextInstance868_25 : Fintype ι]
    [DecidableEq ι]
    [Fintype n]
    [contextInstance869_14 : DecidableEq n] (x : ι → n) (j : n) : content x j ≤ Fintype.card ι :=
  (Finset.card_filter_le _ _).trans_eq (Finset.card_univ)



lemma intertwiner_content_zero
    (L : EuclideanSpace ℂ (ι → n) →ₗ[ℂ] EuclideanSpace ℂ (κ → n))
    (hL : ∀ (g : Matrix.unitaryGroup n ℂ) v, L (rep g v) = rep g (L v))
    (x : ι → n) (y : κ → n) (j : n) (hxy : content x j ≠ content y j) :
    L (EuclideanSpace.single x (1 : ℂ)) y = 0 := by
  let N := Fintype.card ι + Fintype.card κ + 1
  let z : ℂ := Complex.exp (2 * Real.pi * Complex.I / N)
  have hz : IsPrimitiveRoot z N := Complex.isPrimitiveRoot_exp _ (by dsimp [N]; omega)
  have hzn : ‖z‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hz.pow_eq_one (by dsimp [N]; omega)
  have hzu : star z * z = 1 := by
    rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hzn]
    norm_num
  let g : Matrix.unitaryGroup n ℂ := ⟨Matrix.diagonal (fun k => if k = j then z else 1),
    diagonal_unitary_of_star_mul _ (fun k => by split_ifs; exact hzu; simp)⟩
  have hh := congrArg (fun v : EuclideanSpace ℂ (κ → n) => v y)
    (hL g (EuclideanSpace.single x (1 : ℂ)))
  change L (action (Matrix.diagonal _) _) y = action (Matrix.diagonal _) _ y at hh
  rw [diagonal_single, map_smul, action_diagonal] at hh
  simp only [PiLp.smul_apply, smul_eq_mul, phase_product] at hh
  by_contra hn
  apply hxy
  exact hz.pow_inj (by have := content_le_card x j; dsimp [N]; omega)
    (by have := content_le_card y j; dsimp [N]; omega) (mul_right_cancel₀ hn hh)



lemma intertwiner_diagonal
    (L : EuclideanSpace ℂ (ι → n) →ₗ[ℂ] EuclideanSpace ℂ (κ → n))
    (hL : ∀ (g : Matrix.unitaryGroup n ℂ) v, L (rep g v) = rep g (L v))
    (a : n → ℂ) (v : EuclideanSpace ℂ (ι → n)) :
    L (action (Matrix.diagonal a) v) = action (Matrix.diagonal a) (L v) := by
  have hsingle (x : ι → n) :
      L (action (Matrix.diagonal a) (EuclideanSpace.single x (1 : ℂ))) =
        action (Matrix.diagonal a) (L (EuclideanSpace.single x (1 : ℂ))) := by
    ext y
    rw [diagonal_single, map_smul, action_diagonal]
    simp only [PiLp.smul_apply, smul_eq_mul]
    by_cases he : ∀ j, content x j = content y j
    · rw [product_content a x, product_content a y]
      congr 1
      exact Finset.prod_congr rfl fun j _ => congrArg (fun k => a j ^ k) (he j)
    · push Not at he
      obtain ⟨j, hj⟩ := he
      rw [intertwiner_content_zero L hL x y j hj, mul_zero, mul_zero]
  have hexp := (EuclideanSpace.basisFun (ι → n) ℂ).sum_repr v
  simp only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] at hexp
  rw [← hexp, map_sum, map_sum, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [map_smul, map_smul, map_smul, map_smul, hsingle]



lemma intertwiner_hermitian
    (L : EuclideanSpace ℂ (ι → n) →ₗ[ℂ] EuclideanSpace ℂ (κ → n))
    (hL : ∀ (g : Matrix.unitaryGroup n ℂ) v, L (rep g v) = rep g (L v))
    (a : Matrix n n ℂ) (ha : a.IsHermitian) (v : EuclideanSpace ℂ (ι → n)) :
    L (action a v) = action a (L v) := by
  rw [ha.spectral_theorem]
  simp only [Unitary.conjStarAlgAut_apply, map_mul, Module.End.mul_apply]
  change L (rep ha.eigenvectorUnitary (action (Matrix.diagonal _) (rep (star ha.eigenvectorUnitary) v))) = _
  rw [hL, intertwiner_diagonal L hL, hL]
  rfl

end SpinAngle.TensorRep

namespace SpinAngle.TensorRep
open SpinAngle.Specht
variable {ι n : Type*} [contextInstance980_23 : Fintype ι] [contextInstance980_35 : DecidableEq ι] [contextInstance980_51 : Fintype n] [contextInstance980_63 : DecidableEq n]



lemma apply_mem_hermitian (U : Subrepresentation (rep (ι := ι) (n := n)))
    (a : Matrix n n ℂ) (ha : a.IsHermitian)
    (v : EuclideanSpace ℂ (ι → n)) (hv : v ∈ U) : action a v ∈ U := by
  let L : EuclideanSpace ℂ (ι → n) →ₗ[ℂ] EuclideanSpace ℂ (ι → n) :=
    U.toSubmodule.starProjection.toLinearMap
  have hu : ∀ (g : Matrix.unitaryGroup n ℂ) (x y : EuclideanSpace ℂ (ι → n)),
      ⟪rep g x, rep g y⟫_ℂ = ⟪x, y⟫_ℂ := rep_unitary
  have hL : ∀ (g : Matrix.unitaryGroup n ℂ) (w : EuclideanSpace ℂ (ι → n)),
      L (rep g w) = rep g (L w) := by
    intro g w
    exact starProjection_rep (rep (ι := ι) (n := n)) hu U g w
  have hlv : L v = v := U.toSubmodule.starProjection_eq_self_iff.mpr hv
  have hh := intertwiner_hermitian L hL a ha v
  rw [hlv] at hh
  rw [← hh]
  exact U.toSubmodule.starProjection_apply_mem _

end SpinAngle.TensorRep

namespace SpinAngle.PolynomialCarrier
open scoped Classical Matrix
open SpinAngle.Specht SpinAngle.Young
variable (D : YoungDiagram) (q : ℕ) (hq : D.colLen 0 ≤ q)


def highestMonomial (t : Fin q → ℝ) : ℝ := ∏ i : Cells D, t (rowColor D q hq i)

lemma highestMonomial_nonneg (t : Fin q → ℝ) (ht : ∀ j, 0 ≤ t j) :
    0 ≤ highestMonomial D q hq t := Finset.prod_nonneg fun _ _ => ht _



lemma monomial_le_highest (t : Fin q → ℝ) (ht : ∀ j, 0 ≤ t j) (hanti : Antitone t)
    (x : Cells D → Fin q)
    (hinj : ∀ i j : Cells D, i.val.2 = j.val.2 → (x i).val = (x j).val → i = j) :
    (∏ i, t (x i)) ≤ highestMonomial D q hq t := by
  obtain ⟨σ, -, hσ⟩ := column_sort_le D (fun i => (x i).val) hinj
  rw [← Equiv.prod_comp σ (fun i => t (x i))]
  apply Finset.prod_le_prod₀ (fun _ _ => ht _)
  intro i _
  exact hanti (show rowColor D q hq i ≤ x (σ i) from hσ i)



theorem diagonal_norm_bound (t : Fin q → ℝ) (ht : ∀ j, 0 ≤ t j) (hanti : Antitone t)
    (v : TensorSpace D q) (hv : v ∈ alternating D q) :
    ‖TensorRep.action (Matrix.diagonal (fun j => (t j : ℂ))) v‖ ≤
      highestMonomial D q hq t * ‖v‖ := by
  have hb := highestMonomial_nonneg D q hq t ht
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hb (norm_nonneg _))).mp
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  rw [TensorRep.action_diagonal, norm_mul, norm_prod, mul_pow]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ht _)]
  by_cases hz : v x = 0
  · simp [hz]
  · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact pow_le_pow_left₀ (Finset.prod_nonneg fun _ _ => ht _)
      (monomial_le_highest D q hq t ht hanti x (alternating_injective D q v hv x hz)) 2

end SpinAngle.PolynomialCarrier





noncomputable section
open scoped Matrix ComplexOrder
namespace SpinAngle.SortedSpectrum
variable {q : ℕ} (A : Matrix (Fin q) (Fin q) ℂ) (hA : A.IsHermitian)

def values : Fin q → ℝ :=
  (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues (by simp)

def basis : OrthonormalBasis (Fin q) ℂ (EuclideanSpace ℂ (Fin q)) :=
  (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvectorBasis (by simp)

def changeBasis : Matrix.unitaryGroup (Fin q) ℂ :=
  ⟨(EuclideanSpace.basisFun (Fin q) ℂ).toBasis.toMatrix (basis A hA).toBasis,
    (EuclideanSpace.basisFun (Fin q) ℂ).toMatrix_orthonormalBasis_mem_unitary (basis A hA)⟩

@[simp] lemma changeBasis_apply (i j : Fin q) : changeBasis A hA i j = basis A hA j i := rfl

lemma values_antitone : Antitone (values A hA) :=
  LinearMap.IsSymmetric.eigenvalues_antitone _ _

lemma eigenvector (i : Fin q) :
    Matrix.toEuclideanLin A (basis A hA i) = (values A hA i : ℂ) • basis A hA i :=
  LinearMap.IsSymmetric.apply_eigenvectorBasis _ _ _

lemma spectral_theorem : A = (changeBasis A hA : Matrix _ _ ℂ) *
    Matrix.diagonal (fun i => (values A hA i : ℂ)) * star (changeBasis A hA : Matrix _ _ ℂ) := by
  have he : A * (changeBasis A hA : Matrix _ _ ℂ) =
      (changeBasis A hA : Matrix _ _ ℂ) * Matrix.diagonal (fun i => (values A hA i : ℂ)) := by
    ext i j
    rw [Matrix.mul_diagonal]
    simpa only [Matrix.mul_apply, changeBasis_apply,
      Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, PiLp.smul_apply, smul_eq_mul,
      mul_comm] using congrArg (fun v : EuclideanSpace ℂ (Fin q) => v i) (eigenvector A hA j)
  have hh := congrArg (fun B : Matrix (Fin q) (Fin q) ℂ => B * star (changeBasis A hA : Matrix _ _ ℂ)) he
  simpa only [Matrix.mul_assoc, (changeBasis A hA).property.2, Matrix.mul_one] using hh

lemma values_nonneg (hpos : A.PosSemidef) (i : Fin q) : 0 ≤ values A hA i := by
  have hp := (Matrix.isPositive_toEuclideanLin_iff.mpr hpos).inner_nonneg_left (basis A hA i)
  rw [eigenvector, inner_smul_left, (basis A hA).inner_eq_one i] at hp
  have hp' : (0 : ℂ) ≤ (values A hA i : ℂ) := by simpa only [Complex.conj_ofReal, mul_one] using hp
  exact RCLike.ofReal_nonneg.mp hp'

lemma trace_eq_sum : Matrix.trace A = ∑ i, (values A hA i : ℂ) := by
  conv_lhs => rw [spectral_theorem A hA]
  rw [Matrix.trace_mul_cycle, (changeBasis A hA).property.1,
    Matrix.one_mul, Matrix.trace_diagonal]

end SpinAngle.SortedSpectrum

namespace SpinAngle.PolynomialCarrier
open scoped Classical Matrix InnerProductSpace
open SpinAngle.Specht SpinAngle.Young Module
variable (D : YoungDiagram) (q : ℕ) (hq : D.colLen 0 ≤ q)

abbrev Carrier : Type := (ordinary D q hq).toSubmodule

instance carrierInner : InnerProductSpace ℂ (Carrier D q hq) :=
  @Submodule.innerProductSpace ℂ (alternating D q).toSubmodule _ _ inferInstance
    (ordinary D q hq).toSubmodule


def inclusion : Carrier D q hq →ₗᵢ[ℂ] TensorSpace D q :=
  (alternating D q).toSubmodule.subtypeₗᵢ.comp (ordinary D q hq).toSubmodule.subtypeₗᵢ

@[simp] lemma inclusion_apply (v : Carrier D q hq) : inclusion D q hq v = v.val.val := rfl

lemma inclusion_equivariant (g : Matrix.unitaryGroup (Fin q) ℂ) (v : Carrier D q hq) :
    inclusion D q hq ((ordinary D q hq).toRepresentation g v) =
      TensorRep.rep g (inclusion D q hq v) := rfl

def image : Subrepresentation (TensorRep.rep (ι := Cells D) (n := Fin q)) where
  toSubmodule := LinearMap.range (inclusion D q hq).toLinearMap
  apply_mem_toSubmodule := by
    rintro g v ⟨x,rfl⟩
    exact ⟨(ordinary D q hq).toRepresentation g x,rfl⟩

lemma inclusion_image (v : Carrier D q hq) : inclusion D q hq v ∈ image D q hq := ⟨v,rfl⟩


def hermitianAction (a : Matrix (Fin q) (Fin q) ℂ) (ha : a.IsHermitian) :
    Carrier D q hq →ₗ[ℂ] Carrier D q hq :=
  (LinearEquiv.ofInjective (inclusion D q hq).toLinearMap (inclusion D q hq).injective).symm.toLinearMap.comp
    ((TensorRep.action a).comp (inclusion D q hq).toLinearMap |>.codRestrict
      (image D q hq).toSubmodule (fun v => TensorRep.apply_mem_hermitian _ a ha _ (inclusion_image D q hq v)))

@[simp] lemma inclusion_hermitianAction (a : Matrix (Fin q) (Fin q) ℂ) (ha : a.IsHermitian)
    (v : Carrier D q hq) :
    inclusion D q hq (hermitianAction D q hq a ha v) = TensorRep.action a (inclusion D q hq v) := by
  exact congrArg Subtype.val ((LinearEquiv.ofInjective (inclusion D q hq).toLinearMap
    (inclusion D q hq).injective).apply_symm_apply _)

lemma tensor_hermitian (a : Matrix (Fin q) (Fin q) ℂ) (ha : a.IsHermitian) :
    (TensorRep.tensor (fun _ : Cells D => a)).IsHermitian := by
  change star (TensorRep.tensor (fun _ : Cells D => a)) = _
  rw [← TensorRep.tensor_star]
  congr 1
  funext i
  exact ha

lemma hermitianAction_symmetric (a : Matrix (Fin q) (Fin q) ℂ) (ha : a.IsHermitian) :
    LinearMap.IsSymmetric (𝕜 := ℂ) (E := Carrier D q hq) (hermitianAction D q hq a ha) := by
  intro x y
  rw [← (inclusion D q hq).inner_map_map, ← (inclusion D q hq).inner_map_map x,
    inclusion_hermitianAction, inclusion_hermitianAction]
  exact (Matrix.isSymmetric_toEuclideanLin_iff.mpr (tensor_hermitian D q a ha)) x.val.val y.val.val

lemma ordinary_rep_unitary (g : Matrix.unitaryGroup (Fin q) ℂ) (v w : Carrier D q hq) :
    ⟪(ordinary D q hq).toRepresentation g v, (ordinary D q hq).toRepresentation g w⟫_ℂ = ⟪v,w⟫_ℂ :=
  TensorRep.rep_unitary g v.val.val w.val.val

lemma raw_norm_unitary (g : Matrix.unitaryGroup (Fin q) ℂ) (v : TensorSpace D q) :
    ‖TensorRep.rep g v‖ = ‖v‖ :=
  (TensorRep.rep g).isometryOfInner (TensorRep.rep_unitary g) |>.norm_map v


theorem hermitianAction_norm_bound (a : Matrix (Fin q) (Fin q) ℂ) (ha : a.PosSemidef)
    (v : Carrier D q hq) :
    ‖hermitianAction D q hq a ha.isHermitian v‖ ≤
      highestMonomial D q hq (SortedSpectrum.values a ha.isHermitian) * ‖v‖ := by
  rw [← (inclusion D q hq).norm_map (hermitianAction D q hq a ha.isHermitian v),
    inclusion_hermitianAction, ← (inclusion D q hq).norm_map v]
  let u := SortedSpectrum.changeBasis a ha.isHermitian
  let t := SortedSpectrum.values a ha.isHermitian
  have he := SortedSpectrum.spectral_theorem a ha.isHermitian
  have hin : TensorRep.rep u⁻¹ (inclusion D q hq v) ∈ alternating D q :=
    (alternating D q).apply_mem_toSubmodule u⁻¹ v.val.property
  have hb := diagonal_norm_bound D q hq t (SortedSpectrum.values_nonneg a ha.isHermitian ha)
    (SortedSpectrum.values_antitone a ha.isHermitian) _ hin
  change a = (u : Matrix _ _ ℂ) * Matrix.diagonal (fun i => (t i : ℂ)) * (↑(u⁻¹) : Matrix _ _ ℂ) at he
  conv_lhs => rw [he]
  simp only [map_mul, Module.End.mul_apply]
  change ‖TensorRep.rep u (TensorRep.action (Matrix.diagonal _) (TensorRep.rep u⁻¹ _))‖ ≤ _
  rw [raw_norm_unitary]
  simpa only [raw_norm_unitary] using hb

end SpinAngle.PolynomialCarrier




noncomputable section
open scoped TensorProduct InnerProductSpace BigOperators
namespace SpinAngle.ExternalTensor
open Module
variable {E F : Type*} [contextInstance1195_23 : NormedAddCommGroup E] [contextInstance1195_46 : InnerProductSpace ℂ E]
  [contextInstance1196_2 : NormedAddCommGroup F] [contextInstance1196_25 : InnerProductSpace ℂ F]
  [contextInstance1197_2 : FiniteDimensional ℂ E] [contextInstance1197_26 : FiniteDimensional ℂ F]
variable {G H : Type*} [contextInstance1198_23 : Group G] [contextInstance1198_33 : Group H]

def rep (ρ : Representation ℂ G E) (σ : Representation ℂ H F) :
    Representation ℂ (G × H) (E ⊗[ℂ] F) :=
  Representation.tprod (ρ.comp (MonoidHom.fst G H)) (σ.comp (MonoidHom.snd G H))

@[simp] lemma rep_tmul
    {E : Type*} {F : Type*}
    [contextInstance1195_23 : NormedAddCommGroup E]
    [contextInstance1195_46 : InnerProductSpace ℂ E]
    [contextInstance1196_2 : NormedAddCommGroup F]
    [contextInstance1196_25 : InnerProductSpace ℂ F]
    [FiniteDimensional ℂ E]
    [FiniteDimensional ℂ F]
    {G : Type*} {H : Type*}
    [contextInstance1198_23 : Group G]
    [contextInstance1198_33 : Group H] (ρ : Representation ℂ G E) (σ : Representation ℂ H F)
    (g : G × H) (x : E) (y : F) :
    rep ρ σ g (x ⊗ₜ[ℂ] y) = ρ g.1 x ⊗ₜ σ g.2 y := rfl

def rightSlice (β : Module.Dual ℂ F) : E ⊗[ℂ] F →ₗ[ℂ] E :=
  (TensorProduct.rid ℂ E).toLinearMap.comp (TensorProduct.map LinearMap.id β)

def leftSlice (α : Module.Dual ℂ E) : E ⊗[ℂ] F →ₗ[ℂ] F :=
  (TensorProduct.lid ℂ F).toLinearMap.comp (TensorProduct.map α LinearMap.id)

@[simp] lemma rightSlice_tmul
    {E : Type*} {F : Type*}
    [contextInstance1195_23 : NormedAddCommGroup E]
    [contextInstance1195_46 : InnerProductSpace ℂ E]
    [contextInstance1196_2 : NormedAddCommGroup F]
    [contextInstance1196_25 : InnerProductSpace ℂ F]
    [FiniteDimensional ℂ E]
    [FiniteDimensional ℂ F] (β : Module.Dual ℂ F) (x : E) (y : F) :
    rightSlice β (x ⊗ₜ[ℂ] y) = β y • x := rfl
@[simp] lemma leftSlice_tmul
    {E : Type*} {F : Type*}
    [contextInstance1195_23 : NormedAddCommGroup E]
    [contextInstance1195_46 : InnerProductSpace ℂ E]
    [contextInstance1196_2 : NormedAddCommGroup F]
    [contextInstance1196_25 : InnerProductSpace ℂ F]
    [FiniteDimensional ℂ E]
    [FiniteDimensional ℂ F] (α : Module.Dual ℂ E) (x : E) (y : F) :
    leftSlice α (x ⊗ₜ[ℂ] y) = α x • y := rfl

lemma slice_commute
    {E : Type*} {F : Type*}
    [contextInstance1195_23 : NormedAddCommGroup E]
    [contextInstance1195_46 : InnerProductSpace ℂ E]
    [contextInstance1196_2 : NormedAddCommGroup F]
    [contextInstance1196_25 : InnerProductSpace ℂ F]
    [FiniteDimensional ℂ E]
    [FiniteDimensional ℂ F] (α : Module.Dual ℂ E) (β : Module.Dual ℂ F) (v : E ⊗[ℂ] F) :
    α (rightSlice β v) = β (leftSlice α v) := by
  induction v using TensorProduct.inductionOn with
  | tmul x y => simp [mul_comm]
  | add x y hx hy => simp [hx, hy]

lemma slice_map_left
    {E : Type*} {F : Type*}
    [contextInstance1195_23 : NormedAddCommGroup E]
    [contextInstance1195_46 : InnerProductSpace ℂ E]
    [contextInstance1196_2 : NormedAddCommGroup F]
    [contextInstance1196_25 : InnerProductSpace ℂ F]
    [FiniteDimensional ℂ E]
    [FiniteDimensional ℂ F] (β : Module.Dual ℂ F) (A : E →ₗ[ℂ] E) (v : E ⊗[ℂ] F) :
    rightSlice β (TensorProduct.map A LinearMap.id v) = A (rightSlice β v) := by
  induction v using TensorProduct.inductionOn with
  | tmul x y => simp
  | add x y hx hy => simp [hx, hy]

lemma eq_sum_slices
    {E : Type*} {F : Type*}
    [contextInstance1195_23 : NormedAddCommGroup E]
    [contextInstance1195_46 : InnerProductSpace ℂ E]
    [contextInstance1196_2 : NormedAddCommGroup F]
    [contextInstance1196_25 : InnerProductSpace ℂ F]
    [FiniteDimensional ℂ E]
    [FiniteDimensional ℂ F] {ι : Type*} [Fintype ι] (b : Basis ι ℂ F) (v : E ⊗[ℂ] F) :
    v = ∑ i, rightSlice (b.coord i) v ⊗ₜ[ℂ] b i := by
  induction v using TensorProduct.inductionOn with
  | tmul x y =>
    simp only [rightSlice_tmul, TensorProduct.smul_tmul,
      ← TensorProduct.tmul_sum, Basis.coord_apply, Basis.sum_repr]
  | add x y hx hy => simp only [map_add, TensorProduct.add_tmul, Finset.sum_add_distrib, ← hx, ← hy]

lemma rightSlice_ext {v w : E ⊗[ℂ] F}
    (h : ∀ β : Module.Dual ℂ F, rightSlice β v = rightSlice β w) : v = w := by
  classical
  let b := Module.finBasis ℂ F
  rw [eq_sum_slices b v, eq_sum_slices b w]
  exact Finset.sum_congr rfl fun i _ => congrArg (fun x : E => x ⊗ₜ[ℂ] b i) (h _)

lemma scalar_of_commute (ρ : Representation ℂ G E) [ρ.IsIrreducible]
    (A : E →ₗ[ℂ] E) (hA : ∀ g x, A (ρ g x) = ρ g (A x)) :
    ∃ z : ℂ, A = z • LinearMap.id := by
  let f := A.intertwiningMap_of_isIntertwiningMap ρ ρ hA
  obtain ⟨z, hz⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed (ρ := ρ)).surjective f
  refine ⟨z, ?_⟩
  ext x
  exact (congrArg (fun L : ρ.IntertwiningMap ρ => L x) hz).symm


lemma left_commutant (ρ : Representation ℂ G E) [ρ.IsIrreducible]
    (d : E ⊗[ℂ] F →ₗ[ℂ] E ⊗[ℂ] F)
    (hd : ∀ g v, d (TensorProduct.map (ρ g) LinearMap.id v) =
      TensorProduct.map (ρ g) LinearMap.id (d v)) :
    ∃ B : F →ₗ[ℂ] F, d = TensorProduct.map LinearMap.id B := by
  classical
  let : Nontrivial E := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
  obtain ⟨x₀, hx₀⟩ := exists_ne (0 : E)
  obtain ⟨α, hα⟩ := Module.Projective.exists_dual_eq_one ℂ hx₀
  let B : F →ₗ[ℂ] F := (leftSlice α).comp (d.comp (TensorProduct.mk ℂ E F x₀))
  refine ⟨B, ?_⟩
  ext x y
  change d (x ⊗ₜ[ℂ] y) = TensorProduct.map LinearMap.id B (x ⊗ₜ[ℂ] y)
  apply rightSlice_ext
  intro β
  let A : E →ₗ[ℂ] E := (rightSlice β).comp (d.comp ((TensorProduct.mk ℂ E F).flip y))
  have hA (g : G) (v : E) : A (ρ g v) = ρ g (A v) := by
    change rightSlice β (d (ρ g v ⊗ₜ[ℂ] y)) = ρ g (rightSlice β (d (v ⊗ₜ[ℂ] y)))
    rw [← slice_map_left, ← hd]
    rfl
  obtain ⟨z,hz⟩ := scalar_of_commute ρ A hA
  have hzv (v : E) : rightSlice β (d (v ⊗ₜ[ℂ] y)) = z • v :=
    congrArg (fun f : E →ₗ[ℂ] E => f v) hz
  have hzB : β (B y) = z := by
    change β (leftSlice α (d (x₀ ⊗ₜ[ℂ] y))) = z
    rw [← slice_commute, hzv, map_smul, hα, smul_eq_mul, mul_one]
  change rightSlice β (d (x ⊗ₜ[ℂ] y)) = β (B y) • x
  rw [hzv, hzB]

lemma commutant_scalar (ρ : Representation ℂ G E) (σ : Representation ℂ H F)
    [ρ.IsIrreducible] [σ.IsIrreducible]
    (d : (rep ρ σ).IntertwiningMap (rep ρ σ)) :
    ∃ z : ℂ, d.toLinearMap = z • LinearMap.id := by
  obtain ⟨B,hB⟩ := left_commutant ρ d.toLinearMap (by
    intro g v
    simpa [rep, Representation.tprod_apply, Module.End.one_eq_id] using Representation.IntertwiningMap.isIntertwining _ _ d (g,1) v)
  have hσ (h : H) (y : F) : B (σ h y) = σ h (B y) := by
    let : Nontrivial E := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
    obtain ⟨x,hx⟩ := exists_ne (0 : E)
    obtain ⟨α,hα⟩ := Module.Projective.exists_dual_eq_one ℂ hx
    have hh := Representation.IntertwiningMap.isIntertwining _ _ d (1,h) (x ⊗ₜ[ℂ] y)
    change d.toLinearMap (rep ρ σ (1,h) (x ⊗ₜ y)) =
      rep ρ σ (1,h) (d.toLinearMap (x ⊗ₜ y)) at hh
    rw [hB] at hh
    simp only [rep_tmul, map_one, Module.End.one_apply, TensorProduct.map_tmul,
      LinearMap.id_apply] at hh
    have := congrArg (leftSlice α) hh
    simpa [hα] using this
  obtain ⟨z,hz⟩ := scalar_of_commute σ B hσ
  refine ⟨z, ?_⟩
  rw [hB, hz]
  ext x y
  simp

lemma unitary
    {E : Type*} {F : Type*}
    [contextInstance1195_23 : NormedAddCommGroup E]
    [contextInstance1195_46 : InnerProductSpace ℂ E]
    [contextInstance1196_2 : NormedAddCommGroup F]
    [contextInstance1196_25 : InnerProductSpace ℂ F]
    [FiniteDimensional ℂ E]
    [FiniteDimensional ℂ F]
    {G : Type*} {H : Type*}
    [contextInstance1198_23 : Group G]
    [contextInstance1198_33 : Group H] (ρ : Representation ℂ G E) (σ : Representation ℂ H F)
    (hρ : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x,y⟫_ℂ)
    (hσ : ∀ h x y, ⟪σ h x, σ h y⟫_ℂ = ⟪x,y⟫_ℂ)
    (g : G × H) (v w : E ⊗[ℂ] F) :
    ⟪rep ρ σ g v, rep ρ σ g w⟫_ℂ = ⟪v,w⟫_ℂ := by
  let a : E →ₗᵢ[ℂ] E := (ρ g.1).isometryOfInner (hρ g.1)
  let b : F →ₗᵢ[ℂ] F := (σ g.2).isometryOfInner (hσ g.2)
  exact TensorProduct.inner_map_map a b v w

lemma projection_commute (τ : Representation ℂ G E)
    (hτ : ∀ g x y, ⟪τ g x, τ g y⟫_ℂ = ⟪x,y⟫_ℂ)
    (U : Subrepresentation τ) (g : G) (v : E) :
    U.toSubmodule.starProjection (τ g v) = τ g (U.toSubmodule.starProjection v) := by
  apply U.toSubmodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact U.apply_mem_toSubmodule g (U.toSubmodule.starProjection_apply_mem v)
  · intro w hw
    have hw' := U.apply_mem_toSubmodule g⁻¹ hw
    have he : τ g (τ g⁻¹ w) = w := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [← map_sub]
    conv_lhs => rhs; rw [← he]
    rw [hτ]
    exact U.toSubmodule.starProjection_inner_eq_zero v _ hw'



theorem irreducible (ρ : Representation ℂ G E) (σ : Representation ℂ H F)
    [ρ.IsIrreducible] [σ.IsIrreducible]
    (hρ : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x,y⟫_ℂ)
    (hσ : ∀ h x y, ⟪σ h x, σ h y⟫_ℂ = ⟪x,y⟫_ℂ) :
    (rep ρ σ).IsIrreducible := by
  let : Nontrivial E := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
  let : Nontrivial F := IsSimpleModule.nontrivial (MonoidAlgebra ℂ H) σ.asModule
  obtain ⟨x,hx⟩ := exists_ne (0 : E)
  obtain ⟨y,hy⟩ := exists_ne (0 : F)
  have hxy : x ⊗ₜ[ℂ] y ≠ 0 := by
    intro h
    have := congrArg norm h
    simp only [TensorProduct.norm_tmul, norm_zero] at this
    exact (mul_ne_zero (norm_ne_zero_iff.mpr hx) (norm_ne_zero_iff.mpr hy)) this
  have htb : (⊤ : Subrepresentation (rep ρ σ)) ≠ ⊥ := by
    intro h
    have hh : x ⊗ₜ[ℂ] y ∈ (⊤ : Subrepresentation (rep ρ σ)) := by trivial
    rw [h] at hh
    exact hxy hh
  let : Nontrivial (Subrepresentation (rep ρ σ)) := ⟨⟨⊤,⊥,htb⟩⟩
  refine ⟨fun U => ?_⟩
  let d : (rep ρ σ).IntertwiningMap (rep ρ σ) :=
    U.toSubmodule.starProjection.toLinearMap.intertwiningMap_of_isIntertwiningMap _ _
      (projection_commute _ (unitary ρ σ hρ hσ) U)
  obtain ⟨z,hz⟩ := commutant_scalar ρ σ d
  have hproj (v : E ⊗[ℂ] F) : U.toSubmodule.starProjection v = z • v :=
    congrArg (fun f : E ⊗[ℂ] F →ₗ[ℂ] E ⊗[ℂ] F => f v) hz
  by_cases hz0 : z = 0
  · left
    apply bot_unique
    intro v hv
    change v = 0
    have hh := hproj v
    rw [U.toSubmodule.starProjection_eq_self_iff.mpr hv, hz0, zero_smul] at hh
    exact hh
  · right
    apply top_unique
    intro v _
    have hv := U.toSubmodule.starProjection_apply_mem (z⁻¹ • v)
    rw [hproj, smul_smul, mul_inv_cancel₀ hz0, one_smul] at hv
    exact hv

end SpinAngle.ExternalTensor






noncomputable section
open scoped BigOperators ComplexConjugate
namespace SpinAngle.TorusNaturality
open Module
variable {n X Y E F : Type*} [contextInstance1400_29 : Fintype n] [contextInstance1400_41 : Fintype X] [contextInstance1400_53 : Fintype Y]
  [contextInstance1401_2 : AddCommGroup E] [contextInstance1401_19 : Module ℂ E] [contextInstance1401_32 : AddCommGroup F] [contextInstance1401_49 : Module ℂ F]
variable (b : Basis X ℂ E) (c : Basis Y ℂ F)
  (w : X → n → ℕ) (v : Y → n → ℕ)
  (D : (n → ℂ) → E →ₗ[ℂ] E) (D' : (n → ℂ) → F →ₗ[ℂ] F)
  (hb : ∀ a x, D a (b x) = (∏ j, a j ^ w x j) • b x)
  (hc : ∀ a y, D' a (c y) = (∏ j, a j ^ v y j) • c y)

include hc in
lemma repr_diagonal (a : n → ℂ) (f : F) (y : Y) :
    c.repr (D' a f) y = (∏ j, a j ^ v y j) * c.repr f y := by
  classical
  calc
    c.repr (D' a f) y = c.repr (D' a (∑ k, c.repr f k • c k)) y := by rw [c.sum_repr]
    _ = _ := by
      simp only [map_sum, map_smul, hc,
        Basis.repr_self]
      simp [Finset.sum_apply, Finsupp.single_apply, mul_comm]

lemma coefficient_zero
    {n : Type*} {X : Type*} {Y : Type*} {E : Type*} {F : Type*}
    [contextInstance1400_29 : Fintype n]
    [Fintype X]
    [contextInstance1400_53 : Fintype Y]
    [contextInstance1401_2 : AddCommGroup E]
    [contextInstance1401_19 : Module ℂ E]
    [contextInstance1401_32 : AddCommGroup F]
    [contextInstance1401_49 : Module ℂ F]
    (b : Basis X ℂ E) (c : Basis Y ℂ F)
    (w : X → n → ℕ) (v : Y → n → ℕ)
    (D : (n → ℂ) → E →ₗ[ℂ] E) (D' : (n → ℂ) → F →ₗ[ℂ] F)
    (hb : ∀ a x, D a (b x) = (∏ j, a j ^ w x j) • b x)
    (hc : ∀ a y, D' a (c y) = (∏ j, a j ^ v y j) • c y) (L : E →ₗ[ℂ] F)
    (hL : ∀ a : n → ℂ, (∀ j, star (a j) * a j = 1) → ∀ x, L (D a x) = D' a (L x))
    (x : X) (y : Y) (j : n) (hxy : w x j ≠ v y j) :
    c.repr (L (b x)) y = 0 := by
  classical
  let N := w x j + v y j + 1
  let z : ℂ := Complex.exp (2 * Real.pi * Complex.I / N)
  have hN : N ≠ 0 := by dsimp [N]; omega
  have hz : IsPrimitiveRoot z N := Complex.isPrimitiveRoot_exp _ hN
  have hzn : ‖z‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hz.pow_eq_one hN
  have hzu : star z * z = 1 := by
    rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hzn]
    norm_num
  let a : n → ℂ := fun k => if k = j then z else 1
  have ha : ∀ k, star (a k) * a k = 1 := by
    intro k
    dsimp [a]
    split_ifs
    · exact hzu
    · simp
  have hh := congrArg (fun f => c.repr f y) (hL a ha (b x))
  rw [hb, map_smul, map_smul, Finsupp.smul_apply, smul_eq_mul,
    repr_diagonal c v D' hc] at hh
  have hprod (u : n → ℕ) : (∏ k, a k ^ u k) = z ^ u j := by
    simp [a]
  rw [hprod, hprod] at hh
  by_contra hn
  exact hxy (hz.pow_inj (by dsimp [N]; omega) (by dsimp [N]; omega)
    (mul_right_cancel₀ hn hh))

include b c w v hb hc in


theorem diagonal (L : E →ₗ[ℂ] F)
    (hL : ∀ a : n → ℂ, (∀ j, star (a j) * a j = 1) → ∀ x, L (D a x) = D' a (L x))
    (a : n → ℂ) : L.comp (D a) = (D' a).comp L := by
  classical
  apply b.ext
  intro x
  apply c.repr.injective
  ext y
  simp only [LinearMap.comp_apply, hb, map_smul, Finsupp.smul_apply, smul_eq_mul,
    repr_diagonal c v D' hc]
  by_cases hw : w x = v y
  · rw [hw]
  · obtain ⟨j,hj⟩ := Function.ne_iff.mp hw
    rw [coefficient_zero b c w v D D' hb hc L hL x y j hj]
    simp

end SpinAngle.TorusNaturality


namespace SpinAngle.SignedTensor
open scoped Classical Matrix TensorProduct InnerProductSpace
open Module
variable {q : ℕ}
abbrev Spin (q : ℕ) := Fin q × Bool
abbrev Mat (q : ℕ) := Matrix (Fin q) (Fin q) ℂ
abbrev Group (q : ℕ) := Matrix.unitaryGroup (Fin q) ℂ × Matrix.unitaryGroup (Fin q) ℂ

def block : (Mat q × Mat q) →* Matrix (Spin q) (Spin q) ℂ where
  toFun a := Matrix.blockDiagonal (fun b : Bool => cond b a.2 a.1)
  map_one' := by
    convert (Matrix.blockDiagonal_one (m := Fin q) (o := Bool) (α := ℂ)) using 1
    congr 1
    funext b
    cases b <;> rfl
  map_mul' a b := by
    rw [← Matrix.blockDiagonal_mul]
    congr 1
    funext c
    cases c <;> rfl

lemma block_star (a : Mat q × Mat q) : block (star a) = star (block a) := by
  change Matrix.blockDiagonal (fun b : Bool => cond b (star a.2) (star a.1)) = (Matrix.blockDiagonal (fun b : Bool => cond b a.2 a.1))ᴴ
  rw [Matrix.blockDiagonal_conjTranspose]
  congr 1
  funext b
  cases b <;> rfl

def blockGroup : Group q →* Matrix.unitaryGroup (Spin q) ℂ where
  toFun g := ⟨block (g.1.val,g.2.val), by
    rw [Matrix.mem_unitaryGroup_iff', ← block_star, ← map_mul]
    have he : star (g.1.val,g.2.val) * (g.1.val,g.2.val) = 1 :=
      Prod.ext g.1.property.1 g.2.property.1
    rw [he, map_one]⟩
  map_one' := by
    apply Subtype.ext
    change block (1 : Mat q × Mat q) = 1
    exact block.map_one
  map_mul' g h := by
    apply Subtype.ext
    change block ((g.1.val,g.2.val) * (h.1.val,h.2.val)) =
      block (g.1.val,g.2.val) * block (h.1.val,h.2.val)
    exact block.map_mul _ _

variable {ι κ τ : Type*} [contextInstance1517_25 : Fintype ι] [contextInstance1517_37 : DecidableEq ι] [contextInstance1517_53 : Fintype κ] [contextInstance1517_65 : DecidableEq κ]
  [contextInstance1518_2 : Fintype τ] [contextInstance1518_14 : DecidableEq τ]

abbrev Raw := EuclideanSpace ℂ (τ → Spin q)
abbrev PairRaw := EuclideanSpace ℂ (ι → Fin q) ⊗[ℂ] EuclideanSpace ℂ (κ → Fin q)

def rep : Representation ℂ (Group q) (Raw (q := q) (τ := τ)) :=
  (TensorRep.rep (ι := τ)).comp blockGroup

def pairRep : Representation ℂ (Group q) (PairRaw (q := q) (ι := ι) (κ := κ)) :=
  ExternalTensor.rep TensorRep.rep TensorRep.rep

def pairAction : (Mat q × Mat q) →* Module.End ℂ (PairRaw (q := q) (ι := ι) (κ := κ)) where
  toFun a := TensorProduct.map (TensorRep.action a.1) (TensorRep.action a.2)
  map_one' := by
    ext x y
    change TensorProduct.map _ _ (x ⊗ₜ[ℂ] y) = x ⊗ₜ[ℂ] y
    simp only [Prod.fst_one, Prod.snd_one, map_one, TensorProduct.map_tmul,
      Module.End.one_apply]
  map_mul' a b := by
    ext x y
    change TensorProduct.map _ _ (x ⊗ₜ[ℂ] y) =
      TensorProduct.map _ _ (TensorProduct.map _ _ (x ⊗ₜ[ℂ] y))
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul, TensorProduct.map_tmul,
      Module.End.mul_apply]

@[simp] lemma pairAction_tmul (a : Mat q × Mat q)
    (x : EuclideanSpace ℂ (ι → Fin q)) (y : EuclideanSpace ℂ (κ → Fin q)) :
    pairAction a (x ⊗ₜ[ℂ] y) = TensorRep.action a.1 x ⊗ₜ TensorRep.action a.2 y := rfl

lemma pairRep_eq (g : Group q) : pairRep (ι := ι) (κ := κ) g = pairAction (g.1.val,g.2.val) := rfl

lemma rep_unitary (g : Group q) (v w : Raw (q := q) (τ := τ)) :
    ⟪rep g v,rep g w⟫_ℂ = ⟪v,w⟫_ℂ := TensorRep.rep_unitary (blockGroup g) v w

lemma pairRep_unitary (g : Group q) (v w : PairRaw (q := q) (ι := ι) (κ := κ)) :
    ⟪pairRep g v,pairRep g w⟫_ℂ = ⟪v,w⟫_ℂ :=
  ExternalTensor.unitary (TensorRep.rep (ι := ι) (n := Fin q)) (TensorRep.rep (ι := κ) (n := Fin q))
    TensorRep.rep_unitary TensorRep.rep_unitary g v w

def pairBasis : OrthonormalBasis ((ι → Fin q) × (κ → Fin q)) ℂ (PairRaw (q := q) (ι := ι) (κ := κ)) :=
  (EuclideanSpace.basisFun _ ℂ).tensorProduct (EuclideanSpace.basisFun _ ℂ)

def pairContent (x : (ι → Fin q) × (κ → Fin q)) (j : Spin q) : ℕ :=
  cond j.2 (TensorRep.content x.2 j.1) (TensorRep.content x.1 j.1)

def diagPair (a : Spin q → ℂ) : Mat q × Mat q :=
  (Matrix.diagonal (fun j => a (j,false)), Matrix.diagonal (fun j => a (j,true)))

lemma block_diagPair (a : Spin q → ℂ) : block (diagPair a) = Matrix.diagonal a := by
  change Matrix.blockDiagonal (fun b : Bool => cond b (Matrix.diagonal (fun j => a (j,true))) (Matrix.diagonal (fun j => a (j,false)))) = Matrix.diagonal a
  convert Matrix.blockDiagonal_diagonal (fun (b : Bool) (j : Fin q) => a (j,b)) using 1
  congr 1
  funext b
  cases b <;> rfl

lemma pairBasis_diagonal (a : Spin q → ℂ) (x : (ι → Fin q) × (κ → Fin q)) :
    pairAction (diagPair a) (pairBasis x) =
      (∏ j, a j ^ pairContent x j) • pairBasis x := by
  simp only [pairBasis, OrthonormalBasis.tensorProduct_apply', EuclideanSpace.basisFun_apply,
    pairAction_tmul, diagPair, TensorRep.diagonal_single, TensorProduct.smul_tmul,
    TensorProduct.tmul_smul, smul_smul]
  congr 1
  rw [Fintype.prod_prod_type]
  simp only [pairContent, Fintype.prod_bool, Bool.cond_false, Bool.cond_true]
  rw [Finset.prod_mul_distrib, TensorRep.product_content (fun j : Fin q => a (j,true)) x.2,
    TensorRep.product_content (fun j : Fin q => a (j,false)) x.1]



theorem intertwiner_diagonal
    (L : PairRaw (q := q) (ι := ι) (κ := κ) →ₗ[ℂ] Raw (q := q) (τ := τ))
    (hL : ∀ g : Group q, ∀ v, L (pairRep g v) = rep g (L v))
    (a : Spin q → ℂ) (v : PairRaw (q := q) (ι := ι) (κ := κ)) :
    L (pairAction (diagPair a) v) = TensorRep.action (Matrix.diagonal a) (L v) := by
  have hh := TorusNaturality.diagonal (pairBasis (q := q) (ι := ι) (κ := κ)).toBasis
    (EuclideanSpace.basisFun (τ → Spin q) ℂ).toBasis pairContent TensorRep.content
    (fun a => pairAction (diagPair a)) (fun a => TensorRep.action (Matrix.diagonal a))
    pairBasis_diagonal (fun a x => by
      simpa only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply, TensorRep.product_content] using
        (TensorRep.diagonal_single a x)) L (fun a ha v => by
      let g : Group q :=
        (⟨(diagPair a).1, TensorRep.diagonal_unitary_of_star_mul _ (fun j => ha (j,false))⟩,
         ⟨(diagPair a).2, TensorRep.diagonal_unitary_of_star_mul _ (fun j => ha (j,true))⟩)
      have hh := hL g v
      change L (pairAction (diagPair a) v) = TensorRep.action (block (diagPair a)) (L v) at hh
      rwa [block_diagPair] at hh) a
  exact congrArg (fun f : _ →ₗ[ℂ] _ => f v) hh

lemma pair_spectral (a : Mat q × Mat q) (ha : a.1.IsHermitian) (hb : a.2.IsHermitian) :
    ∃ (g : Group q) (d : Spin q → ℂ),
      a = (g.1.val,g.2.val) * diagPair d * (g.1⁻¹.val,g.2⁻¹.val) := by
  refine ⟨(ha.eigenvectorUnitary,hb.eigenvectorUnitary),
    (fun j => cond j.2 (hb.eigenvalues j.1 : ℂ) (ha.eigenvalues j.1 : ℂ)), ?_⟩
  apply Prod.ext
  · exact ha.spectral_theorem
  · exact hb.spectral_theorem



theorem intertwiner_hermitian
    (L : PairRaw (q := q) (ι := ι) (κ := κ) →ₗ[ℂ] Raw (q := q) (τ := τ))
    (hL : ∀ g : Group q, ∀ v, L (pairRep g v) = rep g (L v))
    (a : Mat q × Mat q) (ha : a.1.IsHermitian) (hb : a.2.IsHermitian)
    (v : PairRaw (q := q) (ι := ι) (κ := κ)) :
    L (pairAction a v) = TensorRep.action (block a) (L v) := by
  obtain ⟨g,d,he⟩ := pair_spectral a ha hb
  rw [he]
  simp only [map_mul, Module.End.mul_apply, block_diagPair]
  change L (pairRep g (pairAction (diagPair d) (pairRep g⁻¹ v))) =
    rep g (TensorRep.action (Matrix.diagonal d) (rep g⁻¹ (L v)))
  rw [hL, intertwiner_diagonal L hL, hL]

end SpinAngle.SignedTensor






noncomputable section
open scoped InnerProductSpace
namespace SpinAngle.UnitaryNaturality
variable {G : Type*} [contextInstance1640_21 : Group G]
variable {E F : Type*} [contextInstance1641_23 : NormedAddCommGroup E] [contextInstance1641_46 : InnerProductSpace ℂ E]
  [contextInstance1642_2 : NormedAddCommGroup F] [contextInstance1642_25 : InnerProductSpace ℂ F]
  [contextInstance1643_2 : FiniteDimensional ℂ E] [contextInstance1643_26 : FiniteDimensional ℂ F]
variable (ρ : Representation ℂ G E) (σ : Representation ℂ G F)
  (hρ : ∀ g x y, ⟪ρ g x,ρ g y⟫_ℂ = ⟪x,y⟫_ℂ)
  (hσ : ∀ g x y, ⟪σ g x,σ g y⟫_ℂ = ⟪x,y⟫_ℂ)

lemma inner_move
    {G : Type*}
    [contextInstance1640_21 : Group G]
    {E : Type*}
    [contextInstance1641_23 : NormedAddCommGroup E]
    [contextInstance1641_46 : InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    (ρ : Representation ℂ G E)
    (hρ : ∀ g x y, ⟪ρ g x,ρ g y⟫_ℂ = ⟪x,y⟫_ℂ) (g : G) (x y : E) : ⟪x,ρ g y⟫_ℂ = ⟪ρ g⁻¹ x,y⟫_ℂ := by
  have h := hρ g (ρ g⁻¹ x) y
  simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
    Module.End.one_apply] using h

include hρ hσ in
lemma adjoint_intertwines (L : E →ₗ[ℂ] F)
    (hL : ∀ g x, L (ρ g x) = σ g (L x)) (g : G) (y : F) :
    LinearMap.adjoint L (σ g y) = ρ g (LinearMap.adjoint L y) := by
  apply ext_inner_left ℂ
  intro x
  rw [LinearMap.adjoint_inner_right, inner_move σ hσ, ← hL,
    ← LinearMap.adjoint_inner_right, ← inner_move ρ hρ]

lemma adjoint_isometry (L : E →ₗᵢ[ℂ] F) (x : E) :
    LinearMap.adjoint L.toLinearMap (L x) = x := by
  apply ext_inner_left ℂ
  intro y
  rw [LinearMap.adjoint_inner_right]
  exact L.inner_map_map y x

end SpinAngle.UnitaryNaturality

namespace SpinAngle.SignedCarrier
open scoped Classical TensorProduct InnerProductSpace
open SpinAngle.Young SpinAngle.Specht PolynomialCarrier Module SignedTensor
variable (a b : YoungDiagram) (q : ℕ) (ha : a.colLen 0 ≤ q) (hb : b.colLen 0 ≤ q)

abbrev Carrier := PolynomialCarrier.Carrier a q ha ⊗[ℂ] PolynomialCarrier.Carrier b q hb

instance carrierNormed : NormedAddCommGroup (Carrier a b q ha hb) :=
  TensorProduct.instNormedAddCommGroup (𝕜 := ℂ)
    (E := PolynomialCarrier.Carrier a q ha) (F := PolynomialCarrier.Carrier b q hb)

instance carrierInner : InnerProductSpace ℂ (Carrier a b q ha hb) :=
  TensorProduct.instInnerProductSpace (𝕜 := ℂ)
    (E := PolynomialCarrier.Carrier a q ha) (F := PolynomialCarrier.Carrier b q hb)

instance carrierFinite : FiniteDimensional ℂ (Carrier a b q ha hb) :=
  inferInstanceAs (FiniteDimensional ℂ (PolynomialCarrier.Carrier a q ha ⊗[ℂ] PolynomialCarrier.Carrier b q hb))

abbrev rep : Representation ℂ (Group q) (Carrier a b q ha hb) :=
  ExternalTensor.rep (E := PolynomialCarrier.Carrier a q ha)
    (F := PolynomialCarrier.Carrier b q hb)
    (ordinary a q ha).toRepresentation (ordinary b q hb).toRepresentation

instance irreducible : (rep a b q ha hb).IsIrreducible := by
  let := ordinary_irreducible a q ha
  let := ordinary_irreducible b q hb
  exact ExternalTensor.irreducible _ _ (ordinary_rep_unitary a q ha) (ordinary_rep_unitary b q hb)

def inclusion : Carrier a b q ha hb →ₗᵢ[ℂ]
    PairRaw (q := q) (ι := Cells a) (κ := Cells b) :=
  TensorProduct.mapIsometry (E := PolynomialCarrier.Carrier a q ha) (F := PolynomialCarrier.Carrier b q hb)
    (PolynomialCarrier.inclusion a q ha) (PolynomialCarrier.inclusion b q hb)

lemma inclusion_equivariant (g : Group q) (v : Carrier a b q ha hb) :
    inclusion a b q ha hb (rep a b q ha hb g v) =
      pairRep g (inclusion a b q ha hb v) := by
  induction v using TensorProduct.inductionOn with
  | tmul x y => rfl
  | add x y hx hy => simp [hx,hy]

lemma rep_unitary (g : Group q) (v w : Carrier a b q ha hb) :
    ⟪rep a b q ha hb g v,rep a b q ha hb g w⟫_ℂ = ⟪v,w⟫_ℂ := by
  rw [← (inclusion a b q ha hb).inner_map_map,
    ← (inclusion a b q ha hb).inner_map_map v w,
    inclusion_equivariant, inclusion_equivariant]
  exact SignedTensor.pairRep_unitary g _ _

def hermitianAction (A : Mat q × Mat q) (hA : A.1.IsHermitian) (hB : A.2.IsHermitian) :
    Carrier a b q ha hb →ₗ[ℂ] Carrier a b q ha hb :=
  TensorProduct.map (PolynomialCarrier.hermitianAction a q ha A.1 hA)
    (PolynomialCarrier.hermitianAction b q hb A.2 hB)

lemma inclusion_hermitianAction (A : Mat q × Mat q) (hA : A.1.IsHermitian) (hB : A.2.IsHermitian)
    (v : Carrier a b q ha hb) :
    inclusion a b q ha hb (hermitianAction a b q ha hb A hA hB v) =
      pairAction A (inclusion a b q ha hb v) := by
  induction v using TensorProduct.inductionOn with
  | tmul x y =>
    simp only [inclusion, hermitianAction, TensorProduct.mapIsometry_apply,
      TensorProduct.map_tmul, pairAction_tmul]
    change PolynomialCarrier.inclusion a q ha (PolynomialCarrier.hermitianAction a q ha A.1 hA x) ⊗ₜ[ℂ]
      PolynomialCarrier.inclusion b q hb (PolynomialCarrier.hermitianAction b q hb A.2 hB y) = _
    rw [PolynomialCarrier.inclusion_hermitianAction, PolynomialCarrier.inclusion_hermitianAction]
    rfl
  | add x y hx hy => simp [hx,hy]

variable {τ : Type*} [contextInstance1741_21 : Fintype τ] [contextInstance1741_33 : DecidableEq τ]



theorem intertwiner_hermitian
    (L : (rep a b q ha hb).IntertwiningMap (SignedTensor.rep (q := q) (τ := τ)))
    (A : Mat q × Mat q) (hA : A.1.IsHermitian) (hB : A.2.IsHermitian)
    (v : Carrier a b q ha hb) :
    L (hermitianAction a b q ha hb A hA hB v) = TensorRep.action (block A) (L v) := by
  let J := inclusion a b q ha hb
  let L' := L.toLinearMap.comp (LinearMap.adjoint J.toLinearMap)
  have hequiv (g : Group q) (x : PairRaw (q := q) (ι := Cells a) (κ := Cells b)) :
      L' (pairRep g x) = SignedTensor.rep g (L' x) := by
    dsimp [L']
    rw [UnitaryNaturality.adjoint_intertwines (rep a b q ha hb) pairRep
      (rep_unitary a b q ha hb) SignedTensor.pairRep_unitary J.toLinearMap
      (inclusion_equivariant a b q ha hb), L.isIntertwining]
  have h := SignedTensor.intertwiner_hermitian L' hequiv A hA hB (J v)
  have hj (x : Carrier a b q ha hb) : L' (J x) = L x := by
    dsimp [L']
    rw [UnitaryNaturality.adjoint_isometry]
  rw [← inclusion_hermitianAction a b q ha hb A hA hB v, hj, hj] at h
  exact h

end SpinAngle.SignedCarrier



namespace SpinAngle.TensorRep
variable {ι n : Type*} [contextInstance1770_23 : Fintype ι] [contextInstance1770_35 : DecidableEq ι] [contextInstance1770_51 : Fintype n] [contextInstance1770_63 : DecidableEq n]

lemma continuous_action (v : EuclideanSpace ℂ (ι → n)) :
    Continuous (fun A : Matrix n n ℂ => action A v) := by
  change Continuous (fun A : Matrix n n ℂ =>
    WithLp.toLp 2 (fun x : ι → n => ∑ y, (∏ i, A (x i) (y i)) * v y))
  apply (PiLp.continuous_toLp 2 (fun _ : ι → n => ℂ)).comp
  fun_prop

lemma continuous_rep : Continuous (fun g : Matrix.unitaryGroup n ℂ =>
    (rep (ι := ι) g).toContinuousLinearMap) := by
  apply continuous_clm_apply.mpr
  intro v
  exact (continuous_action v).comp continuous_subtype_val
end SpinAngle.TensorRep

namespace SpinAngle.PolynomialCarrier
open SpinAngle.Young SpinAngle.Specht
variable (D : YoungDiagram) (q : ℕ) (hq : D.colLen 0 ≤ q)
lemma continuous_rep : Continuous (fun g : Matrix.unitaryGroup (Fin q) ℂ =>
    ((ordinary D q hq).toRepresentation g).toContinuousLinearMap) := by
  let : InnerProductSpace ℂ (ordinary D q hq).toSubmodule := carrierInner D q hq
  apply (continuous_clm_apply (𝕜 := ℂ) (E := Carrier D q hq) (F := Carrier D q hq)).mpr
  intro v
  apply (inclusion D q hq).comp_continuous_iff.mp
  change Continuous (fun g : Matrix.unitaryGroup (Fin q) ℂ =>
    TensorRep.rep g (inclusion D q hq v))
  exact continuous_clm_apply.mp (TensorRep.continuous_rep (ι := Cells D) (n := Fin q)) _
end SpinAngle.PolynomialCarrier

namespace SpinAngle.ExternalTensor
open scoped TensorProduct
variable {G H : Type*} [contextInstance1802_23 : Group G] [contextInstance1802_33 : Group H] [contextInstance1802_43 : TopologicalSpace G] [contextInstance1802_64 : TopologicalSpace H]
variable {E F : Type*} [contextInstance1803_23 : NormedAddCommGroup E] [contextInstance1803_46 : InnerProductSpace ℂ E]
  [contextInstance1804_2 : NormedAddCommGroup F] [contextInstance1804_25 : InnerProductSpace ℂ F]
  [contextInstance1805_2 : FiniteDimensional ℂ E] [contextInstance1805_26 : FiniteDimensional ℂ F]
lemma continuous_rep (ρ : Representation ℂ G E) (σ : Representation ℂ H F)
    (hρ : Continuous (fun g => (ρ g).toContinuousLinearMap))
    (hσ : Continuous (fun h => (σ h).toContinuousLinearMap)) :
    Continuous (fun g : G × H => (rep ρ σ g).toContinuousLinearMap) := by
  apply continuous_clm_apply.mpr
  intro v
  induction v using TensorProduct.inductionOn with
  | tmul x y =>
    change Continuous (fun g : G × H => ρ g.1 x ⊗ₜ[ℂ] σ g.2 y)
    exact TensorProduct.continuous_tmul.comp
      (((continuous_clm_apply.mp hρ x).comp continuous_fst).prodMk
        ((continuous_clm_apply.mp hσ y).comp continuous_snd))
  | add x y hx hy =>
    have hh : Continuous (fun g : G × H => (rep ρ σ g).toContinuousLinearMap x +
        (rep ρ σ g).toContinuousLinearMap y) := hx.add hy
    convert hh using 1
    funext g
    exact map_add _ x y
end SpinAngle.ExternalTensor

namespace SpinAngle.SignedTensor
variable {q : ℕ} {τ : Type*} [contextInstance1828_29 : Fintype τ] [contextInstance1828_41 : DecidableEq τ]
lemma continuous_block : Continuous (block (q := q)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun A : Mat q × Mat q => if i.2 = j.2 then (cond i.2 A.2 A.1) i.1 j.1 else 0)
  split_ifs
  · cases i.2 <;> simp only [Bool.cond_false, Bool.cond_true] <;> fun_prop
  · fun_prop

lemma continuous_blockGroup : Continuous (blockGroup (q := q)) := by
  apply Continuous.subtype_mk
  exact continuous_block.comp ((continuous_subtype_val.comp continuous_fst).prodMk
    (continuous_subtype_val.comp continuous_snd))

lemma continuous_rep : Continuous (fun g : Group q => (rep (τ := τ) g).toContinuousLinearMap) :=
  TensorRep.continuous_rep.comp continuous_blockGroup
end SpinAngle.SignedTensor

namespace SpinAngle.SignedCarrier
open SpinAngle.Young SpinAngle.Specht SignedTensor
variable (a b : YoungDiagram) (q : ℕ) (ha : a.colLen 0 ≤ q) (hb : b.colLen 0 ≤ q)
lemma continuous_rep : Continuous (fun g : Group q => (rep a b q ha hb g).toContinuousLinearMap) :=
  ExternalTensor.continuous_rep _ _ (PolynomialCarrier.continuous_rep a q ha)
    (PolynomialCarrier.continuous_rep b q hb)
end SpinAngle.SignedCarrier


namespace SpinAngle.TensorRep
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {ι n : Type*} [contextInstance1859_23 : Fintype ι] [contextInstance1859_35 : DecidableEq ι] [contextInstance1859_51 : Fintype n] [contextInstance1859_63 : DecidableEq n]
lemma tensor_posSemidef (a : ι → Matrix n n ℂ) (ha : ∀ i, (a i).PosSemidef) :
    (tensor a).PosSemidef := by
  let r : ι → Matrix n n ℂ := fun i => CFC.sqrt (a i)
  have he : tensor a = star (tensor r) * tensor r := by
    rw [← tensor_star, ← tensor_mul]
    congr 1
    funext i
    dsimp [r]
    rw [(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (a i))).star_eq,
      CFC.sqrt_mul_sqrt_self (a i) (ha i).nonneg]
  rw [he]
  exact Matrix.posSemidef_conjTranspose_mul_self _

lemma action_positive (a : Matrix n n ℂ) (ha : a.PosSemidef) :
    LinearMap.IsPositive (𝕜 := ℂ) (E := EuclideanSpace ℂ (ι → n)) (action a) :=
  Matrix.isPositive_toEuclideanLin_iff.mpr (tensor_posSemidef (fun _ : ι => a) (fun _ => ha))
end SpinAngle.TensorRep

namespace SpinAngle.PolynomialCarrier
open scoped Classical InnerProductSpace
open SpinAngle.Young SpinAngle.Specht
variable (D : YoungDiagram) (q : ℕ) (hq : D.colLen 0 ≤ q)

lemma hermitianAction_positive (a : Matrix (Fin q) (Fin q) ℂ) (ha : a.PosSemidef) :
    LinearMap.IsPositive (𝕜 := ℂ) (E := Carrier D q hq) (hermitianAction D q hq a ha.isHermitian) := by
  refine ⟨hermitianAction_symmetric D q hq a ha.isHermitian, ?_⟩
  intro x
  rw [← (inclusion D q hq).inner_map_map, inclusion_hermitianAction]
  exact (TensorRep.action_positive a ha).2 (inclusion D q hq x)

def highestVector : Carrier D q hq :=
  ⟨⟨highest D q hq,highest_mem D q hq⟩, self_mem_cyclic _ _⟩

lemma highestVector_ne_zero : highestVector D q hq ≠ 0 := by
  intro h
  have he := congrArg (inclusion D q hq) h
  exact highest_ne_zero D q hq (by simpa [highestVector] using he)

lemma inclusion_linear_hermitianAction (A : Matrix (Fin q) (Fin q) ℂ) (hA : A.IsHermitian)
    (v : Carrier D q hq) :
    (inclusion D q hq).toLinearMap (hermitianAction D q hq A hA v) =
      TensorRep.action A ((inclusion D q hq).toLinearMap v) :=
  inclusion_hermitianAction D q hq A hA v

lemma highestVector_diagonal (t : Fin q → ℝ) :
    hermitianAction D q hq (Matrix.diagonal (fun i => (t i : ℂ)))
      (Matrix.isHermitian_diagonal_iff.mpr (fun i => by simp [IsSelfAdjoint])) (highestVector D q hq) =
        (highestMonomial D q hq t : ℂ) • highestVector D q hq := by
  have hinj : Function.Injective (inclusion D q hq).toLinearMap := by
    intro x y h
    exact Subtype.ext (Subtype.ext h)
  apply hinj
  rw [inclusion_linear_hermitianAction, map_smul]
  change TensorRep.action (Matrix.diagonal (fun i => (t i : ℂ))) (highest D q hq) =
    (highestMonomial D q hq t : ℂ) • highest D q hq
  rw [highest_diagonal]
  congr 1
  exact (map_prod Complex.ofRealHom _ _).symm

lemma card_rowColor (j : Fin q) :
    (Finset.univ.filter fun i : Cells D => rowColor D q hq i = j).card = D.rowLen j := by
  rw [← Fintype.card_subtype]
  calc
    Fintype.card {i : Cells D // rowColor D q hq i = j} = Fintype.card {i : Cells D // i.val.1 = j.val} :=
      Fintype.card_congr (Equiv.subtypeEquivRight (fun i => Fin.ext_iff))
    _ = D.rowLen j := card_row_subtype D j

lemma highestMonomial_eq_rowLen (t : Fin q → ℝ) :
    highestMonomial D q hq t = ∏ j : Fin q, t j ^ D.rowLen j := by
  unfold highestMonomial
  rw [← Finset.prod_fiberwise' Finset.univ (rowColor D q hq) t]
  simp only [Finset.prod_const, card_rowColor]

include hq in
lemma sum_rowLen_eq_card : ∑ j : Fin q, D.rowLen j = Fintype.card (Cells D) := by
  have h := Finset.sum_fiberwise Finset.univ (rowColor D q hq) (fun _ : Cells D => (1 : ℕ))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, card_rowColor, Finset.card_univ] at h
  exact_mod_cast h

end SpinAngle.PolynomialCarrier




noncomputable section
open scoped TensorProduct InnerProductSpace ComplexOrder
namespace SpinAngle.TensorPositive
variable {E F : Type*} [contextInstance1947_23 : NormedAddCommGroup E] [contextInstance1947_46 : InnerProductSpace ℂ E]
  [contextInstance1948_2 : NormedAddCommGroup F] [contextInstance1948_25 : InnerProductSpace ℂ F]
  [contextInstance1949_2 : FiniteDimensional ℂ E] [contextInstance1949_26 : FiniteDimensional ℂ F]

lemma mapL_nonneg (A : E →L[ℂ] E) (B : F →L[ℂ] F) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    0 ≤ TensorProduct.mapL A B := by
  let a := CFC.sqrt A
  let b := CFC.sqrt B
  have ha : star a = a := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg A)).star_eq
  have hb : star b = b := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg B)).star_eq
  have hstar : star (TensorProduct.mapL a b) = TensorProduct.mapL a b := by
    change ContinuousLinearMap.adjoint (TensorProduct.mapL a b) = _
    rw [TensorProduct.adjoint_mapL]
    change TensorProduct.mapL (star a) (star b) = _
    rw [ha,hb]
  have he : star (TensorProduct.mapL a b) * TensorProduct.mapL a b = TensorProduct.mapL A B := by
    rw [hstar, ← TensorProduct.mapL_mul]
    dsimp [a,b]
    rw [CFC.sqrt_mul_sqrt_self A hA, CFC.sqrt_mul_sqrt_self B hB]
  rw [← he]
  exact star_mul_self_nonneg _

lemma map_positive (A : E →ₗ[ℂ] E) (B : F →ₗ[ℂ] F) (hA : A.IsPositive) (hB : B.IsPositive) :
    (TensorProduct.map A B).IsPositive := by
  have ha : 0 ≤ A.toContinuousLinearMap :=
    (ContinuousLinearMap.nonneg_iff_isPositive).mpr hA
  have hb : 0 ≤ B.toContinuousLinearMap :=
    (ContinuousLinearMap.nonneg_iff_isPositive).mpr hB
  have h := (ContinuousLinearMap.nonneg_iff_isPositive).mp (mapL_nonneg _ _ ha hb)
  change ((TensorProduct.mapL A.toContinuousLinearMap B.toContinuousLinearMap).toLinearMap).IsPositive at h
  simpa only [TensorProduct.toLinearMap_mapL, LinearMap.coe_toContinuousLinearMap] using h

lemma map_norm_bound (A : E →ₗ[ℂ] E) (B : F →ₗ[ℂ] F)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : ∀ x, ‖A x‖ ≤ a * ‖x‖) (hB : ∀ y, ‖B y‖ ≤ b * ‖y‖)
    (v : E ⊗[ℂ] F) : ‖TensorProduct.map A B v‖ ≤ (a*b)*‖v‖ := by
  have ha' : ‖A.toContinuousLinearMap‖ ≤ a :=
    ContinuousLinearMap.opNorm_le_bound _ ha hA
  have hb' : ‖B.toContinuousLinearMap‖ ≤ b :=
    ContinuousLinearMap.opNorm_le_bound _ hb hB
  calc
    ‖TensorProduct.map A B v‖ ≤ ‖TensorProduct.mapL A.toContinuousLinearMap B.toContinuousLinearMap‖ * ‖v‖ :=
      by simpa only [TensorProduct.mapL_apply, LinearMap.coe_toContinuousLinearMap] using
        (ContinuousLinearMap.le_opNorm (TensorProduct.mapL A.toContinuousLinearMap B.toContinuousLinearMap) v)
    _ ≤ (a*b)*‖v‖ := mul_le_mul_of_nonneg_right
      ((TensorProduct.norm_mapL_le _ _).trans (mul_le_mul ha' hb' (norm_nonneg _) ha)) (norm_nonneg _)
end SpinAngle.TensorPositive




noncomputable section
open scoped BigOperators
namespace SpinAngle.EntropyMonomial
variable {ι : Type*} [contextInstance2001_21 : Fintype ι]

def entropy (n : ι → ℕ) : ℝ :=
  (∑ i, n i : ℕ) * Real.log (∑ i, n i : ℕ) - ∑ i, (n i : ℝ) * Real.log (n i)

lemma sum_log_ratio (n : ι → ℕ) (p : ℕ) (hp : 0 < p) (hn : ∑ i, n i = p) :
    ∑ i, (n i : ℝ) * Real.log ((n i : ℝ) / p) = -entropy n := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have he (i : ι) : (n i : ℝ) * Real.log ((n i : ℝ) / p) =
      (n i : ℝ) * Real.log (n i) - (n i : ℝ) * Real.log p := by
    by_cases hi : n i = 0
    · simp [hi]
    · rw [Real.log_div (by exact_mod_cast hi) hp0, mul_sub]
  simp only [he, Finset.sum_sub_distrib, ← Finset.sum_mul]
  have hn' : ∑ i, (n i : ℝ) = p := by exact_mod_cast hn
  rw [hn']
  simp only [entropy, hn]
  ring

lemma power_le_exponential (k p : ℕ) (hp : 0 < p) (t : ℝ) (ht : 0 ≤ t) :
    t ^ k ≤ Real.exp ((k : ℝ) * Real.log ((k : ℝ) / p) + p * t - k) := by
  by_cases hk : k = 0
  · subst k
    simpa using (Real.one_le_exp_iff.mpr (mul_nonneg (Nat.cast_nonneg p) ht))
  by_cases ht0 : t = 0
  · simp only [ht0, zero_pow hk]
    exact (Real.exp_pos _).le
  have hk' : 0 < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
  have hp' : 0 < (p : ℝ) := by exact_mod_cast hp
  have ht' : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  have hr : 0 < (k : ℝ) / p := div_pos hk' hp'
  have hlog := Real.log_le_sub_one_of_pos (div_pos ht' hr)
  rw [Real.log_div ht0 hr.ne'] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog hk'.le
  have hc : (k : ℝ) * (t / ((k : ℝ) / p) - 1) = p * t - k := by
    field_simp
    
  rw [hc] at hmul
  calc
    t ^ k = Real.exp ((k : ℝ) * Real.log t) := by
      rw [Real.exp_nat_mul, Real.exp_log ht']
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)



theorem prod_pow_le (n : ι → ℕ) (t : ι → ℝ) (ht : ∀ i, 0 ≤ t i)
    (hsum : ∑ i, t i ≤ 1) :
    ∏ i, t i ^ n i ≤ Real.exp (-entropy n) := by
  classical
  let p : ℕ := ∑ i, n i
  by_cases hp : p = 0
  · have hn : ∀ i, n i = 0 := by
      intro i
      have hle := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => Nat.zero_le (n j)) (Finset.mem_univ i)
      change n i ≤ p at hle
      omega
    simp [entropy, hn]
  have hp' : 0 < p := Nat.pos_of_ne_zero hp
  calc
    ∏ i, t i ^ n i ≤ ∏ i, Real.exp ((n i : ℝ) * Real.log ((n i : ℝ) / p) + p * t i - n i) :=
      Finset.prod_le_prod₀ (fun i _ => pow_nonneg (ht i) _) (fun i _ => power_le_exponential _ p hp' _ (ht i))
    _ = Real.exp (∑ i, ((n i : ℝ) * Real.log ((n i : ℝ) / p) + p * t i - n i)) :=
      (Real.exp_sum _ _).symm
    _ ≤ Real.exp (-entropy n) := by
      apply Real.exp_le_exp.mpr
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [sum_log_ratio n p hp' rfl]
      have hn : ∑ i, (n i : ℝ) = p := by simp [p]
      rw [hn]
      have h := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg p : (0 : ℝ) ≤ p)
      nlinarith

lemma optimal_prod (n : ι → ℕ) (p : ℕ) (hp : 0 < p) (hn : ∑ i, n i = p) :
    ∏ i, ((n i : ℝ) / p) ^ n i = Real.exp (-entropy n) := by
  rw [← sum_log_ratio n p hp hn, Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : n i = 0
  · simp [hi]
  have hpos : 0 < (n i : ℝ) / p := div_pos (by exact_mod_cast Nat.pos_of_ne_zero hi) (by exact_mod_cast hp)
  rw [Real.exp_nat_mul, Real.exp_log hpos]

end SpinAngle.EntropyMonomial



noncomputable section
open scoped InnerProductSpace ComplexOrder BigOperators
namespace SpinAngle.PositiveTrace
variable {E : Type*} [contextInstance2090_21 : NormedAddCommGroup E] [contextInstance2090_44 : InnerProductSpace ℂ E]
  [contextInstance2091_2 : FiniteDimensional ℂ E]

lemma eigenvalues_nonneg (A : E →ₗ[ℂ] E) (hA : A.IsPositive)
    (i : Fin (Module.finrank ℂ E)) : 0 ≤ hA.isSymmetric.eigenvalues rfl i := by
  have h := hA.inner_nonneg_right (hA.isSymmetric.eigenvectorBasis rfl i)
  rw [hA.isSymmetric.apply_eigenvectorBasis rfl i, inner_smul_right,
    (hA.isSymmetric.eigenvectorBasis rfl).inner_eq_one] at h
  simpa only [mul_one, RCLike.ofReal_nonneg] using h


theorem eigenvalue_le_trace (A : E →ₗ[ℂ] E) (hA : A.IsPositive)
    (v : E) (hv : v ≠ 0) (t : ℝ) (he : A v = (t : ℂ) • v) :
    t ≤ (LinearMap.trace ℂ E A).re := by
  classical
  let b := hA.isSymmetric.eigenvectorBasis rfl
  have hcoord : ∃ i, b.repr v i ≠ 0 := by
    by_contra! hh
    apply hv
    apply b.repr.injective
    ext i
    simpa using hh i
  obtain ⟨i,hi⟩ := hcoord
  have h := congrArg (fun x : E => b.repr x i) he
  rw [hA.isSymmetric.eigenvectorBasis_apply_self_apply, map_smul, PiLp.smul_apply,
    smul_eq_mul] at h
  have ht : hA.isSymmetric.eigenvalues rfl i = t := by
    exact Complex.ofReal_injective (mul_right_cancel₀ hi h)
  change t ≤ RCLike.re (LinearMap.trace ℂ E A)
  rw [hA.isSymmetric.re_trace_eq_sum_eigenvalues rfl, ← ht]
  exact Finset.single_le_sum (fun j _ => eigenvalues_nonneg A hA j) (Finset.mem_univ i)

end SpinAngle.PositiveTrace





noncomputable section
open scoped InnerProductSpace BigOperators ComplexOrder
namespace SpinAngle.Isotypic
variable {G : Type*} [contextInstance2131_21 : Group G]
variable {E F : Type*} [contextInstance2132_23 : NormedAddCommGroup E] [contextInstance2132_46 : InnerProductSpace ℂ E]
  [contextInstance2133_2 : NormedAddCommGroup F] [contextInstance2133_25 : InnerProductSpace ℂ F]
  [contextInstance2134_2 : FiniteDimensional ℂ E] [contextInstance2134_26 : FiniteDimensional ℂ F]
variable (ρ : Representation ℂ G E) (σ : Representation ℂ G F)

def space : Subrepresentation σ where
  toSubmodule := Submodule.span ℂ (Set.range fun z : ρ.IntertwiningMap σ × E => z.1 z.2)
  apply_mem_toSubmodule := by
    intro g v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨⟨f,x⟩,rfl⟩ := hv
      apply Submodule.subset_span
      refine ⟨⟨f,ρ g x⟩, ?_⟩
      exact Representation.IntertwiningMap.isIntertwining ρ σ f g x
    | zero => simp
    | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
    | smul a x hx ih => simpa only [map_smul] using Submodule.smul_mem _ a ih

def projection : F →L[ℂ] F := (space ρ σ).toSubmodule.starProjection

lemma projection_mem
    {G : Type*}
    [contextInstance2131_21 : Group G]
    {E : Type*} {F : Type*}
    [contextInstance2132_23 : NormedAddCommGroup E]
    [contextInstance2132_46 : InnerProductSpace ℂ E]
    [contextInstance2133_2 : NormedAddCommGroup F]
    [contextInstance2133_25 : InnerProductSpace ℂ F]
    [FiniteDimensional ℂ E]
    [contextInstance2134_26 : FiniteDimensional ℂ F]
    (ρ : Representation ℂ G E) (σ : Representation ℂ G F) (v : F) : projection ρ σ v ∈ space ρ σ :=
  (space ρ σ).toSubmodule.starProjection_apply_mem v

lemma projection_norm_apply_le
    {G : Type*}
    [contextInstance2131_21 : Group G]
    {E : Type*} {F : Type*}
    [contextInstance2132_23 : NormedAddCommGroup E]
    [contextInstance2132_46 : InnerProductSpace ℂ E]
    [contextInstance2133_2 : NormedAddCommGroup F]
    [contextInstance2133_25 : InnerProductSpace ℂ F]
    [FiniteDimensional ℂ E]
    [contextInstance2134_26 : FiniteDimensional ℂ F]
    (ρ : Representation ℂ G E) (σ : Representation ℂ G F) (v : F) : ‖projection ρ σ v‖ ≤ ‖v‖ :=
  (space ρ σ).toSubmodule.norm_starProjection_apply_le v

lemma map_mem
    {G : Type*}
    [contextInstance2131_21 : Group G]
    {E : Type*} {F : Type*}
    [contextInstance2132_23 : NormedAddCommGroup E]
    [contextInstance2132_46 : InnerProductSpace ℂ E]
    [contextInstance2133_2 : NormedAddCommGroup F]
    [contextInstance2133_25 : InnerProductSpace ℂ F]
    [FiniteDimensional ℂ E]
    [FiniteDimensional ℂ F]
    (ρ : Representation ℂ G E) (σ : Representation ℂ G F) (f : ρ.IntertwiningMap σ) (x : E) : f x ∈ space ρ σ :=
  Submodule.subset_span ⟨⟨f,x⟩,rfl⟩

lemma endomorphism_mem (d : σ.IntertwiningMap σ) (v : F) (hv : v ∈ space ρ σ) :
    d v ∈ space ρ σ := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨⟨f,x⟩,rfl⟩ := hv
    exact map_mem ρ σ (d.comp f) x
  | zero => simp only [map_zero]; exact (space ρ σ).toSubmodule.zero_mem
  | add x y hx hy ihx ihy => rw [map_add]; exact (space ρ σ).toSubmodule.add_mem ihx ihy
  | smul a x hx ih => rw [map_smul]; exact (space ρ σ).toSubmodule.smul_mem a ih

lemma natural_mem (a : E →ₗ[ℂ] E) (A : F →ₗ[ℂ] F)
    (h : ∀ f : ρ.IntertwiningMap σ, ∀ x, A (f x) = f (a x))
    (v : F) (hv : v ∈ space ρ σ) : A v ∈ space ρ σ := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨⟨f,x⟩,rfl⟩ := hv
    rw [h]
    exact map_mem ρ σ f _
  | zero => simp only [map_zero]; exact (space ρ σ).toSubmodule.zero_mem
  | add x y hx hy ihx ihy => rw [map_add]; exact (space ρ σ).toSubmodule.add_mem ihx ihy
  | smul z x hx ih => rw [map_smul]; exact (space ρ σ).toSubmodule.smul_mem z ih

lemma scalar_on_space
    {G : Type*}
    [contextInstance2131_21 : Group G]
    {E : Type*} {F : Type*}
    [contextInstance2132_23 : NormedAddCommGroup E]
    [contextInstance2132_46 : InnerProductSpace ℂ E]
    [contextInstance2133_2 : NormedAddCommGroup F]
    [contextInstance2133_25 : InnerProductSpace ℂ F]
    [FiniteDimensional ℂ E]
    [FiniteDimensional ℂ F]
    (ρ : Representation ℂ G E) (σ : Representation ℂ G F) (A : F →ₗ[ℂ] F) (c : ℂ)
    (h : ∀ f : ρ.IntertwiningMap σ, ∀ x, A (f x) = c • f x)
    (v : F) (hv : v ∈ space ρ σ) : A v = c • v := by
  induction hv using Submodule.span_induction with
  | mem v hv => obtain ⟨⟨f,x⟩,rfl⟩ := hv; exact h f x
  | zero => simp
  | add x y hx hy ihx ihy => simp [ihx, ihy, smul_add]
  | smul z x hx ih => simp [ih, smul_comm c z]

lemma exists_nonzero_adjoint (v : F) (hv : v ∈ space ρ σ) (hv0 : v ≠ 0) :
    ∃ f : ρ.IntertwiningMap σ, LinearMap.adjoint f.toLinearMap v ≠ 0 := by
  by_contra! hn
  have horth (w : F) (hw : w ∈ space ρ σ) : ⟪w,v⟫_ℂ = 0 := by
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨⟨f,x⟩,rfl⟩ := hw
      change ⟪f.toLinearMap x,v⟫_ℂ = 0
      rw [← LinearMap.adjoint_inner_right, hn]
      simp
    | zero => simp
    | add x y hx hy ihx ihy => simp [ihx, ihy]
    | smul z x hx ih => simp [ih]
  exact hv0 (inner_self_eq_zero.mp (horth v hv))

lemma transfer_eigenvalue_bound (a : E →ₗ[ℂ] E) (A : F →ₗ[ℂ] F)
    (ha : a.IsSymmetric) (hA : A.IsSymmetric)
    (hnat : ∀ f : ρ.IntertwiningMap σ, ∀ x, A (f x) = f (a x))
    (c : ℝ) (hc : ∀ x, ‖a x‖ ≤ c * ‖x‖)
    (v : F) (hv : v ∈ space ρ σ) (hv0 : v ≠ 0)
    (t : ℂ) (ht : A v = t • v) : ‖t‖ ≤ c := by
  obtain ⟨f,hf⟩ := exists_nonzero_adjoint ρ σ v hv hv0
  have he : A.comp f.toLinearMap = f.toLinearMap.comp a := by ext x; exact hnat f x
  have hadj := congrArg LinearMap.adjoint he
  rw [LinearMap.adjoint_comp, LinearMap.adjoint_comp, ha.adjoint_eq, hA.adjoint_eq] at hadj
  have hev : a (LinearMap.adjoint f.toLinearMap v) = t • LinearMap.adjoint f.toLinearMap v := by
    have hh := congrArg (fun L : F →ₗ[ℂ] E => L v) hadj
    simpa only [LinearMap.comp_apply, ht, map_smul] using hh.symm
  have hh := hc (LinearMap.adjoint f.toLinearMap v)
  rw [hev, norm_smul] at hh
  exact (mul_le_mul_iff_left₀ (norm_pos_iff.mpr hf)).mp hh



theorem norm_bound (a : E →ₗ[ℂ] E) (A : F →ₗ[ℂ] F)
    (ha : a.IsSymmetric) (hA : A.IsSymmetric)
    (hnat : ∀ f : ρ.IntertwiningMap σ, ∀ x, A (f x) = f (a x))
    (c : ℝ) (hc0 : 0 ≤ c) (hc : ∀ x, ‖a x‖ ≤ c * ‖x‖)
    (v : F) (hv : v ∈ space ρ σ) : ‖A v‖ ≤ c * ‖v‖ := by
  classical
  let S := (space ρ σ).toSubmodule
  have hinv : ∀ w ∈ S, A w ∈ S := natural_mem ρ σ a A hnat
  let B : S →ₗ[ℂ] S := A.restrict hinv
  have hB : B.IsSymmetric := hA.restrict_invariant hinv
  let b := hB.eigenvectorBasis rfl
  have hb (i : Fin (Module.finrank ℂ S)) : ‖(hB.eigenvalues rfl i : ℂ)‖ ≤ c := by
    apply transfer_eigenvalue_bound ρ σ a A ha hA hnat c hc (b i).val (b i).property
    · intro hh
      have hn := b.orthonormal.ne_zero i
      exact hn (Subtype.ext hh)
    · exact congrArg Subtype.val (hB.apply_eigenvectorBasis rfl i)
  let w : S := ⟨v,hv⟩
  change ‖B w‖ ≤ c * ‖w‖
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc0 (norm_nonneg _))).mp
  rw [← b.repr.norm_map (B w), ← b.repr.norm_map w, mul_pow,
    EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [hB.eigenvectorBasis_apply_self_apply, norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hb i) 2) (sq_nonneg _)

lemma projection_commute_of_invariant
    {G : Type*}
    [Group G]
    {F : Type*}
    [contextInstance2133_2 : NormedAddCommGroup F]
    [contextInstance2133_25 : InnerProductSpace ℂ F]
    [contextInstance2134_26 : FiniteDimensional ℂ F] (S : Submodule ℂ F) (A : F →ₗ[ℂ] F)
    (hA : A.IsSymmetric) (hinv : ∀ v ∈ S, A v ∈ S) (v : F) :
    S.starProjection (A v) = A (S.starProjection v) := by
  apply S.eq_starProjection_of_mem_of_inner_eq_zero
  · exact hinv _ (S.starProjection_apply_mem v)
  · intro w hw
    rw [← map_sub, hA]
    exact S.starProjection_inner_eq_zero v _ (hinv _ hw)

lemma projection_commute_endomorphism (d : σ.IntertwiningMap σ)
    (hd : d.toLinearMap.IsSymmetric) (v : F) :
    projection ρ σ (d v) = d (projection ρ σ v) :=
  projection_commute_of_invariant (G := G) _ d.toLinearMap hd (endomorphism_mem ρ σ d) v

lemma projection_commute_natural (a : E →ₗ[ℂ] E) (A : F →ₗ[ℂ] F)
    (hA : A.IsSymmetric)
    (h : ∀ f : ρ.IntertwiningMap σ, ∀ x, A (f x) = f (a x)) (v : F) :
    projection ρ σ (A v) = A (projection ρ σ v) :=
  projection_commute_of_invariant (G := G) _ A hA (natural_mem ρ σ a A h) v

end SpinAngle.Isotypic

namespace SpinAngle.SignedTensor
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {q : ℕ}

def IsEvenDensity (A : Mat q × Mat q) : Prop :=
  A.1.PosSemidef ∧ A.2.PosSemidef ∧ Matrix.trace A.1 + Matrix.trace A.2 = 1

lemma block_posSemidef (A : Mat q × Mat q) (hA : A.1.PosSemidef) (hB : A.2.PosSemidef) :
    (block A).PosSemidef := by
  let R : Mat q × Mat q := (CFC.sqrt A.1, CFC.sqrt A.2)
  have he : block A = star (block R) * block R := by
    rw [← block_star, ← map_mul]
    congr 1
    apply Prod.ext
    · change A.1 = star (CFC.sqrt A.1) * CFC.sqrt A.1
      rw [(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg A.1)).star_eq,
        CFC.sqrt_mul_sqrt_self A.1 hA.nonneg]
    · change A.2 = star (CFC.sqrt A.2) * CFC.sqrt A.2
      rw [(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg A.2)).star_eq,
        CFC.sqrt_mul_sqrt_self A.2 hB.nonneg]
  rw [he]
  exact Matrix.posSemidef_conjTranspose_mul_self _
end SpinAngle.SignedTensor

namespace SpinAngle.SignedCarrier
open scoped Classical TensorProduct BigOperators InnerProductSpace
open SpinAngle.Young SpinAngle.Specht SignedTensor
variable (a b : YoungDiagram) (q : ℕ) (ha : a.colLen 0 ≤ q) (hb : b.colLen 0 ≤ q)

lemma hermitianAction_positive (A : Mat q × Mat q) (hA : A.1.PosSemidef) (hB : A.2.PosSemidef) :
    LinearMap.IsPositive (𝕜 := ℂ) (E := Carrier a b q ha hb)
      (hermitianAction a b q ha hb A hA.isHermitian hB.isHermitian) :=
  TensorPositive.map_positive (E := PolynomialCarrier.Carrier a q ha)
    (F := PolynomialCarrier.Carrier b q hb) _ _
    (PolynomialCarrier.hermitianAction_positive a q ha A.1 hA)
    (PolynomialCarrier.hermitianAction_positive b q hb A.2 hB)

lemma hermitianAction_norm_bound (A : Mat q × Mat q) (hA : A.1.PosSemidef) (hB : A.2.PosSemidef)
    (v : Carrier a b q ha hb) :
    ‖hermitianAction a b q ha hb A hA.isHermitian hB.isHermitian v‖ ≤
      (PolynomialCarrier.highestMonomial a q ha (SortedSpectrum.values A.1 hA.isHermitian) *
       PolynomialCarrier.highestMonomial b q hb (SortedSpectrum.values A.2 hB.isHermitian)) * ‖v‖ := by
  apply TensorPositive.map_norm_bound (E := PolynomialCarrier.Carrier a q ha)
    (F := PolynomialCarrier.Carrier b q hb)
  · exact Finset.prod_nonneg (fun i _ => SortedSpectrum.values_nonneg A.1 hA.isHermitian hA _)
  · exact Finset.prod_nonneg (fun i _ => SortedSpectrum.values_nonneg A.2 hB.isHermitian hB _)
  · exact PolynomialCarrier.hermitianAction_norm_bound a q ha A.1 hA
  · exact PolynomialCarrier.hermitianAction_norm_bound b q hb A.2 hB

def parts : Fin q ⊕ Fin q → ℕ := Sum.elim (fun i => a.rowLen i) (fun i => b.rowLen i)
def entropy : ℝ := EntropyMonomial.entropy (parts a b q)
def dimension : ℕ := Module.finrank ℂ (Carrier a b q ha hb)

include ha hb in
lemma sum_parts : ∑ i, parts a b q i = Fintype.card (Cells a) + Fintype.card (Cells b) := by
  rw [Fintype.sum_sum_type]
  change (∑ i : Fin q, a.rowLen i) + (∑ i : Fin q, b.rowLen i) = _
  rw [PolynomialCarrier.sum_rowLen_eq_card a q ha, PolynomialCarrier.sum_rowLen_eq_card b q hb]

include ha hb in
lemma entropy_eq_source : entropy a b q =
    (Fintype.card (Cells a) + Fintype.card (Cells b) : ℕ) *
      Real.log (Fintype.card (Cells a) + Fintype.card (Cells b) : ℕ) -
      (∑ i : Fin q, (a.rowLen i : ℝ) * Real.log (a.rowLen i)) -
      (∑ i : Fin q, (b.rowLen i : ℝ) * Real.log (b.rowLen i)) := by
  unfold entropy EntropyMonomial.entropy
  rw [sum_parts a b q ha hb, Fintype.sum_sum_type]
  simp only [parts, Sum.elim_inl, Sum.elim_inr]
  ring

lemma hermitianAction_density_bound (A : Mat q × Mat q) (hA : IsEvenDensity A)
    (v : Carrier a b q ha hb) :
    ‖hermitianAction a b q ha hb A hA.1.isHermitian hA.2.1.isHermitian v‖ ≤
      Real.exp (-entropy a b q) * ‖v‖ := by
  apply (hermitianAction_norm_bound a b q ha hb A hA.1 hA.2.1 v).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  rw [PolynomialCarrier.highestMonomial_eq_rowLen, PolynomialCarrier.highestMonomial_eq_rowLen]
  let t : Fin q ⊕ Fin q → ℝ := Sum.elim
    (SortedSpectrum.values A.1 hA.1.isHermitian) (SortedSpectrum.values A.2 hA.2.1.isHermitian)
  have ht (i) : 0 ≤ t i := by
    cases i with
    | inl i => exact SortedSpectrum.values_nonneg A.1 hA.1.isHermitian hA.1 i
    | inr i => exact SortedSpectrum.values_nonneg A.2 hA.2.1.isHermitian hA.2.1 i
  have hs : ∑ i, t i = 1 := by
    rw [Fintype.sum_sum_type]
    have he1 := SortedSpectrum.trace_eq_sum A.1 hA.1.isHermitian
    have he2 := SortedSpectrum.trace_eq_sum A.2 hA.2.1.isHermitian
    have h : (∑ i, (SortedSpectrum.values A.1 hA.1.isHermitian i : ℂ)) +
        (∑ i, (SortedSpectrum.values A.2 hA.2.1.isHermitian i : ℂ)) = 1 :=
      (congrArg₂ (· + ·) he1.symm he2.symm).trans hA.2.2
    have hh := congrArg Complex.re h
    simpa only [t, Sum.elim_inl, Sum.elim_inr, Complex.add_re, Complex.re_sum, Complex.ofReal_re, Complex.one_re] using hh
  have h := EntropyMonomial.prod_pow_le (parts a b q) t ht hs.le
  simpa only [Fintype.prod_sum_type, parts, t, entropy, Sum.elim_inl, Sum.elim_inr] using h

end SpinAngle.SignedCarrier

namespace SpinAngle.EntropyMonomial
open scoped BigOperators
variable {ι : Type*} [contextInstance2379_21 : Fintype ι] [contextInstance2379_33 : Nonempty ι]

lemma exists_optimal (n : ι → ℕ) : ∃ t : ι → ℝ,
    (∀ i, 0 ≤ t i) ∧ (∑ i, t i = 1) ∧ (∏ i, t i ^ n i = Real.exp (-entropy n)) := by
  classical
  let p := ∑ i, n i
  by_cases hp : p = 0
  · have hn : ∀ i, n i = 0 := by
      intro i
      have h := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => Nat.zero_le (n j)) (Finset.mem_univ i)
      change n i ≤ p at h
      omega
    let i₀ := Classical.choice (inferInstance : Nonempty ι)
    refine ⟨fun i => if i = i₀ then 1 else 0, ?_, ?_, ?_⟩
    · intro i; dsimp only; split_ifs <;> norm_num
    · simp
    · simp [hn, entropy]
  · refine ⟨fun i => (n i : ℝ) / p, fun i => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _), ?_, ?_⟩
    · rw [← Finset.sum_div]
      have he : ∑ i, (n i : ℝ) = p := by simp [p]
      rw [he, div_self (by exact_mod_cast hp)]
    · exact optimal_prod n p (Nat.pos_of_ne_zero hp) rfl
end SpinAngle.EntropyMonomial

namespace SpinAngle.SignedCarrier
open scoped Classical TensorProduct BigOperators InnerProductSpace ComplexOrder
open SpinAngle.Young SpinAngle.Specht SignedTensor
variable (a b : YoungDiagram) (q : ℕ) (ha : a.colLen 0 ≤ q) (hb : b.colLen 0 ≤ q)
variable {τ : Type*} [contextInstance2407_21 : Fintype τ] [contextInstance2407_33 : DecidableEq τ]

abbrev typeProjection : Raw (q := q) (τ := τ) →L[ℂ] Raw (q := q) (τ := τ) :=
  Isotypic.projection (rep a b q ha hb) SignedTensor.rep

lemma density_on_space (A : Mat q × Mat q) (hA : IsEvenDensity A)
    (v : Raw (q := q) (τ := τ))
    (hv : v ∈ Isotypic.space (rep a b q ha hb) (SignedTensor.rep (q := q) (τ := τ))) :
    ‖TensorRep.action (block A) v‖ ≤ Real.exp (-entropy a b q) * ‖v‖ := by
  exact Isotypic.norm_bound (E := Carrier a b q ha hb) (F := Raw (q := q) (τ := τ))
    (rep a b q ha hb) (SignedTensor.rep (q := q) (τ := τ))
    (hermitianAction a b q ha hb A hA.1.isHermitian hA.2.1.isHermitian)
    (TensorRep.action (block A))
    (hermitianAction_positive a b q ha hb A hA.1 hA.2.1).isSymmetric
    (TensorRep.action_positive (block A) (block_posSemidef A hA.1 hA.2.1)).isSymmetric
    (fun L x => (intertwiner_hermitian a b q ha hb L A hA.1.isHermitian hA.2.1.isHermitian x).symm)
    (Real.exp (-entropy a b q)) (Real.exp_pos _).le
    (hermitianAction_density_bound a b q ha hb A hA) v hv

lemma projected_density_bound (A : Mat q × Mat q) (hA : IsEvenDensity A)
    (v : Raw (q := q) (τ := τ)) :
    ‖TensorRep.action (block A) (typeProjection a b q ha hb v)‖ ≤
      Real.exp (-entropy a b q) * ‖v‖ := by
  exact (density_on_space a b q ha hb A hA _
    (Isotypic.projection_mem (rep a b q ha hb) (SignedTensor.rep (q := q) (τ := τ)) v)).trans
    (mul_le_mul_of_nonneg_left
      (Isotypic.projection_norm_apply_le (rep a b q ha hb) (SignedTensor.rep (q := q) (τ := τ)) v)
      (Real.exp_pos _).le)


theorem global_density_upper (A : Mat q × Mat q) (hA : IsEvenDensity A) :
    ‖LinearMap.toContinuousLinearMap (TensorRep.action (ι := τ) (block A)) *
      typeProjection (τ := τ) a b q ha hb‖ ≤ Real.exp (-entropy a b q) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le
  intro v
  exact projected_density_bound a b q ha hb A hA v

def highestVector : Carrier a b q ha hb :=
  PolynomialCarrier.highestVector a q ha ⊗ₜ[ℂ] PolynomialCarrier.highestVector b q hb

lemma highestVector_ne_zero : highestVector a b q ha hb ≠ 0 := by
  intro h
  have hn := congrArg norm h
  rw [highestVector, TensorProduct.norm_tmul (E := PolynomialCarrier.Carrier a q ha)
    (F := PolynomialCarrier.Carrier b q hb), norm_zero] at hn
  exact (mul_ne_zero (norm_ne_zero_iff.mpr (PolynomialCarrier.highestVector_ne_zero a q ha))
    (norm_ne_zero_iff.mpr (PolynomialCarrier.highestVector_ne_zero b q hb))) hn

lemma highestVector_diagonal (t : Fin q ⊕ Fin q → ℝ) :
    hermitianAction a b q ha hb
      (Matrix.diagonal (fun i => (t (.inl i) : ℂ)), Matrix.diagonal (fun i => (t (.inr i) : ℂ)))
      (Matrix.isHermitian_diagonal_iff.mpr (fun i => by simp [IsSelfAdjoint]))
      (Matrix.isHermitian_diagonal_iff.mpr (fun i => by simp [IsSelfAdjoint]))
      (highestVector a b q ha hb) =
        ((∏ i, t i ^ parts a b q i : ℝ) : ℂ) • highestVector a b q ha hb := by
  rw [hermitianAction, highestVector, TensorProduct.map_tmul,
    PolynomialCarrier.highestVector_diagonal, PolynomialCarrier.highestVector_diagonal,
    TensorProduct.smul_tmul_smul, PolynomialCarrier.highestMonomial_eq_rowLen,
    PolynomialCarrier.highestMonomial_eq_rowLen]
  congr 1
  rw [Fintype.prod_sum_type, Complex.ofReal_mul]
  rfl


lemma exists_density_trace_lower [Nonempty (Fin q)] : ∃ (A : Mat q × Mat q) (hA : IsEvenDensity A),
    Real.exp (-entropy a b q) ≤
      (LinearMap.trace ℂ (Carrier a b q ha hb)
        (hermitianAction a b q ha hb A hA.1.isHermitian hA.2.1.isHermitian)).re := by
  obtain ⟨t,ht,hs,he⟩ := EntropyMonomial.exists_optimal (parts a b q)
  let A : Mat q × Mat q :=
    (Matrix.diagonal (fun i => (t (.inl i) : ℂ)), Matrix.diagonal (fun i => (t (.inr i) : ℂ)))
  have hA : IsEvenDensity A := by
    refine ⟨Matrix.PosSemidef.diagonal (fun i => by simpa using ht (.inl i)),
      Matrix.PosSemidef.diagonal (fun i => by simpa using ht (.inr i)), ?_⟩
    simp only [A, Matrix.trace_diagonal]
    have hh := congrArg Complex.ofReal hs
    simpa only [Fintype.sum_sum_type, Complex.ofReal_add, Complex.ofReal_sum, Complex.ofReal_one] using hh
  refine ⟨A,hA,?_⟩
  apply PositiveTrace.eigenvalue_le_trace _ (hermitianAction_positive a b q ha hb A hA.1 hA.2.1)
    (highestVector a b q ha hb) (highestVector_ne_zero a b q ha hb)
  have h := highestVector_diagonal a b q ha hb t
  rw [he] at h
  exact h
end SpinAngle.SignedCarrier


noncomputable section
open scoped BigOperators
namespace SpinAngle.DenseLU

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

def border {n : ℕ} (a : ℂ) (b c : Fin n → ℂ) (D : Mat n) : Mat (n+1) :=
  fun i => Fin.cases (Fin.cases a b) (fun i => Fin.cases (c i) (D i)) i

@[simp] lemma border_zero_zero {n : ℕ} (a : ℂ) (b c : Fin n → ℂ) (D : Mat n) :
    border a b c D 0 0 = a := rfl
@[simp] lemma border_zero_succ {n : ℕ} (a : ℂ) (b c : Fin n → ℂ) (D : Mat n) (j : Fin n) :
    border a b c D 0 j.succ = b j := rfl
@[simp] lemma border_succ_zero {n : ℕ} (a : ℂ) (b c : Fin n → ℂ) (D : Mat n) (i : Fin n) :
    border a b c D i.succ 0 = c i := rfl
@[simp] lemma border_succ_succ {n : ℕ} (a : ℂ) (b c : Fin n → ℂ) (D : Mat n) (i j : Fin n) :
    border a b c D i.succ j.succ = D i j := rfl

lemma border_eq {n : ℕ} (A : Mat (n+1)) :
    border (A 0 0) (fun j => A 0 j.succ) (fun i => A i.succ 0)
      (fun i j => A i.succ j.succ) = A := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> rfl

lemma continuous_border {X : Type*} [TopologicalSpace X] {n : ℕ}
    {a : X → ℂ} {b c : X → Fin n → ℂ} {D : X → Mat n}
    (ha : Continuous a) (hb : Continuous b) (hc : Continuous c) (hD : Continuous D) :
    Continuous (fun x => border (a x) (b x) (c x) (D x)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · exact ha
  · exact (continuous_apply j).comp hb
  · exact (continuous_apply i).comp hc
  · exact (continuous_apply j).comp ((continuous_apply i).comp hD)


lemma border_factor {n : ℕ} (a : ℂ) (ha : a ≠ 0) (b c : Fin n → ℂ) (L U : Mat n) :
    border 1 0 (fun i => c i / a) L * border a b 0 U =
      border a b c (L * U + (Matrix.of fun i j => c i / a * b j)) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · simp [Matrix.mul_apply, Fin.sum_univ_succ]
  · simp [Matrix.mul_apply, Fin.sum_univ_succ]
  · simp [Matrix.mul_apply, Fin.sum_univ_succ, ha]
  · simp [Matrix.mul_apply, Fin.sum_univ_succ, add_comm]

def LowerUnipotent {n : ℕ} (L : Mat n) : Prop :=
  L.IsLowerTriangular ∧ ∀ i, L i i = 1

lemma lower_border {n : ℕ} (c : Fin n → ℂ) (L : Mat n) (hL : LowerUnipotent L) :
    LowerUnipotent (border 1 0 c L) := by
  constructor
  · intro i j hij
    change i < j at hij
    induction i using Fin.cases <;> induction j using Fin.cases
    · simp at hij
    · rfl
    · simp at hij
    · exact hL.1 (by simpa using hij)
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · rfl
    · exact hL.2 i

lemma upper_border {n : ℕ} (a : ℂ) (b : Fin n → ℂ) (U : Mat n) (hU : U.IsUpperTriangular) :
    (border a b 0 U).IsUpperTriangular := by
  intro i j hij
  induction i using Fin.cases <;> induction j using Fin.cases
  · simp at hij
  · simp at hij
  · rfl
  · exact hU (by simpa using hij)

def bigCell (n : ℕ) : Set (Mat n) :=
  {A | ∃ L U, LowerUnipotent L ∧ U.IsUpperTriangular ∧ A = L * U}

lemma border_mem_bigCell {n : ℕ} (a : ℂ) (ha : a ≠ 0) (b c : Fin n → ℂ) (S : Mat n)
    (hS : S ∈ bigCell n) :
    border a b c (S + (Matrix.of fun i j => c i / a * b j)) ∈ bigCell (n+1) := by
  obtain ⟨L,U,hL,hU,rfl⟩ := hS
  exact ⟨border 1 0 (fun i => c i / a) L, border a b 0 U,
    lower_border _ _ hL, upper_border _ _ _ hU, (border_factor a ha b c L U).symm⟩



theorem dense_bigCell (n : ℕ) : Dense (bigCell n) := by
  induction n with
  | zero =>
    intro A
    apply subset_closure
    refine ⟨1,1,?_,?_,?_⟩
    · refine ⟨?_,?_⟩ <;> intro i <;> exact Fin.elim0 i
    · intro i; exact Fin.elim0 i
    · exact Subsingleton.elim _ _
  | succ n ih =>
    have hpivot (a : ℂ) (ha : a ≠ 0) (b c : Fin n → ℂ) (D : Mat n) :
        border a b c D ∈ closure (bigCell (n+1)) := by
      let X : Mat n := fun i j => c i / a * b j
      have hf : Continuous (fun S : Mat n => border a b c (S + X)) :=
        continuous_border continuous_const continuous_const continuous_const
          (continuous_id.add continuous_const)
      have hh := map_mem_closure hf (ih (D-X))
        (fun S hS => border_mem_bigCell a ha b c S hS)
      change border a b c (D - X + X) ∈ closure (bigCell (n+1)) at hh
      simpa only [sub_add_cancel] using hh
    intro A
    let b : Fin n → ℂ := fun j => A 0 j.succ
    let c : Fin n → ℂ := fun i => A i.succ 0
    let D : Mat n := fun i j => A i.succ j.succ
    have hf : Continuous (fun a : ℂ => border a b c D) :=
      continuous_border continuous_id continuous_const continuous_const continuous_const
    have hh := map_mem_closure hf ((dense_compl_singleton (0 : ℂ)) (A 0 0))
      (fun a ha => hpivot a (by simpa using ha) b c D)
    simpa only [closure_closure, b, c, D, border_eq] using hh

end SpinAngle.DenseLU

namespace SpinAngle.PolynomialCarrier
open scoped Classical Matrix
open SpinAngle.Specht SpinAngle.Young
variable (D : YoungDiagram) (q : ℕ) (hq : D.colLen 0 ≤ q)

lemma action_mem_alternating (A : Matrix (Fin q) (Fin q) ℂ)
    (v : TensorSpace D q) (hv : v ∈ alternating D q) :
    TensorRep.action A v ∈ alternating D q := by
  intro g
  rw [← action_site_commute, hv g, map_smul]

lemma upper_weight_support (U : Matrix (Fin q) (Fin q) ℂ) (hU : U.IsUpperTriangular)
    (x : Cells D → Fin q) (hx : TensorRep.action U (highest D q hq) x ≠ 0) :
    ∑ i, (x i).val = ∑ i : Cells D, i.val.1 := by
  have hl := rowRankSum_le D (fun i => (x i).val)
    (alternating_injective D q _ (action_mem_alternating D q U _ (highest_mem D q hq)) x hx)
  apply le_antisymm _ hl
  change (∑ y, (∏ i, U (x i) (y i)) * highest D q hq y) ≠ 0 at hx
  obtain ⟨y, -, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
  have hyv : highest D q hq y ≠ 0 := (mul_ne_zero_iff.mp hy).2
  have hp : ∀ i, x i ≤ y i := by
    intro i
    by_contra hi
    have hz : U (x i) (y i) = 0 := hU (lt_of_not_ge hi)
    exact (mul_ne_zero_iff.mp hy).1 (Finset.prod_eq_zero (Finset.mem_univ i) hz)
  rw [← weight_eigen_support D q hq _ (highest_weight_eigen D q hq) y hyv]
  exact Finset.sum_le_sum fun i _ => hp i



lemma upper_highest (U : Matrix (Fin q) (Fin q) ℂ) (hU : U.IsUpperTriangular) :
    TensorRep.action U (highest D q hq) =
      (TensorRep.action U (highest D q hq) (rowColor D q hq)) • highest D q hq := by
  ext x
  change _ = _ * highest D q hq x
  by_cases hw : ∑ i, (x i).val = ∑ i : Cells D, i.val.1
  · exact alternating_minimal_weight D q hq _
      (action_mem_alternating D q U _ (highest_mem D q hq)) x hw
  · have hv0 : TensorRep.action U (highest D q hq) x = 0 := by
      by_contra hn
      exact hw (upper_weight_support D q hq U hU x hn)
    have he0 : highest D q hq x = 0 := by
      by_contra hn
      exact hw (weight_eigen_support D q hq _ (highest_weight_eigen D q hq) x hn)
    rw [hv0, he0, mul_zero]

lemma continuous_action_highest :
    Continuous (fun A : Matrix (Fin q) (Fin q) ℂ => TensorRep.action A (highest D q hq)) := by
  change Continuous (fun A : Matrix (Fin q) (Fin q) ℂ =>
    WithLp.toLp 2 (fun x : Cells D → Fin q => ∑ y, (∏ i, A (x i) (y i)) * highest D q hq y))
  apply (PiLp.continuous_toLp 2 (fun _ : Cells D → Fin q => ℂ)).comp
  fun_prop



lemma action_highest_mem_of_lower (S : Submodule ℂ (TensorSpace D q))
    (hS : ∀ L : Matrix (Fin q) (Fin q) ℂ, DenseLU.LowerUnipotent L →
      TensorRep.action L (highest D q hq) ∈ S)
    (A : Matrix (Fin q) (Fin q) ℂ) : TensorRep.action A (highest D q hq) ∈ S := by
  have hsub : DenseLU.bigCell q ⊆
      (fun B : Matrix (Fin q) (Fin q) ℂ => TensorRep.action B (highest D q hq)) ⁻¹'
        (S : Set (TensorSpace D q)) := by
    intro B hB
    obtain ⟨L,U,hL,hU,rfl⟩ := hB
    change TensorRep.action (L * U) (highest D q hq) ∈ S
    rw [map_mul, Module.End.mul_apply, upper_highest D q hq U hU, map_smul]
    exact S.smul_mem _ (hS L hL)
  exact closure_minimal hsub
    (S.closed_of_finiteDimensional.preimage (continuous_action_highest D q hq))
    (DenseLU.dense_bigCell q A)

end SpinAngle.PolynomialCarrier
noncomputable section
open scoped BigOperators
namespace SpinAngle.PolyDimension
open MvPolynomial Module
variable (σ : Type*) [contextInstance2689_21 : Fintype σ] [contextInstance2689_33 : DecidableEq σ] (p : ℕ)


def boundedExponentEquiv : {f : σ →₀ ℕ // ∀ i, f i ≤ p} ≃ (σ → Fin (p+1)) where
  toFun f i := ⟨f.val i, Nat.lt_succ_of_le (f.property i)⟩
  invFun f := ⟨Finsupp.equivFunOnFinite.symm (fun i => (f i).val), by
    intro i; exact Nat.le_of_lt_succ (f i).isLt⟩
  left_inv f := by apply Subtype.ext; ext i; rfl
  right_inv f := by funext i; apply Fin.ext; rfl


theorem finrank_restrictDegree :
    Module.finrank ℂ (restrictDegree σ ℂ p) = (p+1) ^ Fintype.card σ := by
  let s : Set (σ →₀ ℕ) := {f | ∀ i, f i ≤ p}
  let : Fintype s := Fintype.ofEquiv (σ → Fin (p+1)) (boundedExponentEquiv σ p).symm
  change Module.finrank ℂ (restrictSupport ℂ s) = _
  rw [Module.finrank_eq_card_basis (basisRestrictSupport ℂ s)]
  calc
    Fintype.card s = Fintype.card (σ → Fin (p+1)) := Fintype.card_congr (boundedExponentEquiv σ p)
    _ = _ := by simp

abbrev LowerIndex (q : ℕ) := (i : Fin q) × Fin i.val

lemma card_lowerIndex (q : ℕ) : Fintype.card (LowerIndex q) = q * (q-1) / 2 := by
  simp only [LowerIndex, Fintype.card_sigma, Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => i) q, Finset.sum_range_id]

lemma twice_card_lowerIndex (q : ℕ) : 2 * Fintype.card (LowerIndex q) = q * (q-1) := by
  simp only [LowerIndex, Fintype.card_sigma, Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => i) q, mul_comm, Finset.sum_range_id_mul_two]

variable {q : ℕ}
def lowerEntry (i j : Fin q) : MvPolynomial (LowerIndex q) ℂ :=
  if h : j < i then X ⟨i, ⟨j.val, h⟩⟩ else if i = j then 1 else 0

lemma lowerEntry_degree (i j : Fin q) : (lowerEntry i j).totalDegree ≤ 1 := by
  unfold lowerEntry
  split_ifs <;> simp

lemma totalDegree_sum_le
    (σ : Type*)
    [Fintype σ]
    [DecidableEq σ]
    (p : ℕ) {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ ℂ)
    (hf : ∀ i ∈ s, (f i).totalDegree ≤ p) : (∑ i ∈ s, f i).totalDegree ≤ p :=
  (MvPolynomial.totalDegree_finsetSum s f).trans (Finset.sup_le hf)

end SpinAngle.PolyDimension

namespace SpinAngle.PolyDimension
open MvPolynomial Module
variable {σ X : Type*} [contextInstance2737_23 : Fintype σ] [contextInstance2737_35 : DecidableEq σ] [contextInstance2737_51 : Fintype X] (p : ℕ)




def valueTranspose (P : X → restrictDegree σ ℂ p) :
    Module.Dual ℂ (restrictDegree σ ℂ p) →ₗ[ℂ] EuclideanSpace ℂ X where
  toFun φ := WithLp.toLp 2 (fun x => φ (P x))
  map_add' φ ψ := by ext x; rfl
  map_smul' c φ := by ext x; rfl

lemma value_mem_range
    {σ : Type*} {X : Type*}
    [Fintype σ]
    [DecidableEq σ]
    [Fintype X]
    (p : ℕ) (P : X → restrictDegree σ ℂ p) (a : σ → ℂ) :
    WithLp.toLp 2 (fun x => MvPolynomial.aeval a (P x).val) ∈
      LinearMap.range (valueTranspose p P) := by
  refine ⟨(MvPolynomial.aeval a).toLinearMap.comp (restrictDegree σ ℂ p).subtype, ?_⟩
  rfl

lemma finrank_value_range
    {σ : Type*} {X : Type*}
    [contextInstance2737_23 : Fintype σ]
    [contextInstance2737_35 : DecidableEq σ]
    [Fintype X]
    (p : ℕ) (P : X → restrictDegree σ ℂ p) :
    Module.finrank ℂ (LinearMap.range (valueTranspose p P)) ≤ (p+1)^Fintype.card σ := by
  have hh := (valueTranspose p P).finrank_range_le
  rw [Subspace.dual_finrank_eq, finrank_restrictDegree] at hh
  exact hh

end SpinAngle.PolyDimension

namespace SpinAngle.PolynomialCarrier
open scoped Classical Matrix
open SpinAngle.Specht SpinAngle.Young PolyDimension MvPolynomial
variable (D : YoungDiagram) (q : ℕ) (hq : D.colLen 0 ≤ q)


def lowerCoordinate (x : Cells D → Fin q) : MvPolynomial (LowerIndex q) ℂ :=
  ∑ y : Cells D → Fin q, (∏ i : Cells D, lowerEntry (x i) (y i)) * C (highest D q hq y)

lemma lowerCoordinate_degree (x : Cells D → Fin q) :
    (lowerCoordinate D q hq x).totalDegree ≤ Fintype.card (Cells D) := by
  apply PolyDimension.totalDegree_sum_le
  intro y _
  apply (MvPolynomial.totalDegree_mul _ _).trans
  rw [MvPolynomial.totalDegree_C, add_zero]
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans
  exact (Finset.sum_le_sum fun i _ => lowerEntry_degree (x i) (y i)).trans_eq (by simp)

def lowerCoordinateBounded (x : Cells D → Fin q) :
    restrictDegree (LowerIndex q) ℂ (Fintype.card (Cells D)) :=
  ⟨lowerCoordinate D q hq x,
    restrictTotalDegree_le_restrictDegree _ _ _
      ((mem_restrictTotalDegree _ _ _).mpr (lowerCoordinate_degree D q hq x))⟩

def lowerParameters (L : Matrix (Fin q) (Fin q) ℂ) (z : LowerIndex q) : ℂ :=
  L z.1 ⟨z.2.val, z.2.isLt.trans z.1.isLt⟩

lemma eval_lowerEntry (L : Matrix (Fin q) (Fin q) ℂ) (hL : DenseLU.LowerUnipotent L)
    (i j : Fin q) : aeval (lowerParameters q L) (lowerEntry i j) = L i j := by
  unfold lowerEntry
  split_ifs with hlt heq
  · simp [aeval_X, lowerParameters]
  · subst j; simp [hL.2 i]
  · have hij : i < j := lt_of_le_of_ne (le_of_not_gt hlt) heq
    rw [map_zero, hL.1 hij]

lemma eval_lowerCoordinate (L : Matrix (Fin q) (Fin q) ℂ) (hL : DenseLU.LowerUnipotent L)
    (x : Cells D → Fin q) :
    aeval (lowerParameters q L) (lowerCoordinate D q hq x) =
      TensorRep.action L (highest D q hq) x := by
  simp only [lowerCoordinate, map_sum, map_mul, map_prod, eval_lowerEntry q L hL]
  change (∑ y : Cells D → Fin q, (∏ i, L (x i) (y i)) *
    aeval (lowerParameters q L) (C (highest D q hq y))) =
      ∑ y : Cells D → Fin q, (∏ i, L (x i) (y i)) * highest D q hq y
  apply Finset.sum_congr rfl
  intro y _
  simp



theorem ordinary_finrank_le :
    Module.finrank ℂ (ordinary D q hq).toSubmodule ≤
      (Fintype.card (Cells D)+1) ^ (q*(q-1)/2) := by
  let P := lowerCoordinateBounded D q hq
  let S := LinearMap.range (PolyDimension.valueTranspose (Fintype.card (Cells D)) P)
  have hL (L : Matrix (Fin q) (Fin q) ℂ) (hL : DenseLU.LowerUnipotent L) :
      TensorRep.action L (highest D q hq) ∈ S := by
    have hh := PolyDimension.value_mem_range (Fintype.card (Cells D)) P (lowerParameters q L)
    have he : WithLp.toLp 2 (fun x => aeval (lowerParameters q L) (P x).val) =
        TensorRep.action L (highest D q hq) := by
      ext x; exact eval_lowerCoordinate D q hq L hL x
    rw [he] at hh
    exact hh
  let inc : (ordinary D q hq).toSubmodule →ₗ[ℂ] TensorSpace D q :=
    (alternating D q).toSubmodule.subtype.comp (ordinary D q hq).toSubmodule.subtype
  have hcarrier (v : (alternating D q).toSubmodule)
      (hv : v ∈ (ordinary D q hq).toSubmodule) : (v : TensorSpace D q) ∈ S := by
    change v ∈ Submodule.span ℂ (Set.range fun g =>
      (alternating D q).toRepresentation g
        (⟨highest D q hq, highest_mem D q hq⟩ : (alternating D q).toSubmodule)) at hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨g,rfl⟩ := hv
      exact action_highest_mem_of_lower D q hq S hL g.val
    | zero => exact S.zero_mem
    | add x y hx hy ihx ihy => exact S.add_mem ihx ihy
    | smul a x hx ih => exact S.smul_mem a ih
  have hinc (v : (ordinary D q hq).toSubmodule) : inc v ∈ S := hcarrier v.val v.property
  let f : (ordinary D q hq).toSubmodule →ₗ[ℂ] S := LinearMap.codRestrict S inc hinc
  have hf : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun v : S => v.val) he
  have hh := LinearMap.finrank_le_finrank_of_injective hf
  exact hh.trans (by
    simpa only [PolyDimension.card_lowerIndex] using
      PolyDimension.finrank_value_range (Fintype.card (Cells D)) P)

end SpinAngle.PolynomialCarrier


noncomputable section
open MeasureTheory TopologicalSpace Set
open scoped BigOperators
namespace SpinAngle.CompactTwirl

variable {G : Type*} [contextInstance2861_21 : Group G] [contextInstance2861_31 : TopologicalSpace G] [contextInstance2861_52 : IsTopologicalGroup G]
  [contextInstance2862_2 : CompactSpace G] [contextInstance2862_19 : MeasurableSpace G] [contextInstance2862_39 : BorelSpace G]

def compactHaar : Measure G :=
  Measure.haarMeasure (⟨⟨Set.univ, isCompact_univ⟩, by simp⟩ : PositiveCompacts G)

instance : IsProbabilityMeasure (compactHaar (G := G)) where
  measure_univ := Measure.haarMeasure_self

instance : (compactHaar (G := G)).IsMulLeftInvariant :=
  inferInstanceAs (Measure.IsMulLeftInvariant (Measure.haarMeasure _))

lemma continuous_integrable {A : Type*} [NormedAddCommGroup A] (f : G → A)
    (hf : Continuous f) : Integrable f (compactHaar (G := G)) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

variable {A : Type*} [contextInstance2877_21 : NormedRing A] [contextInstance2877_36 : NormedAlgebra ℝ A] [contextInstance2877_56 : CompleteSpace A]


def conjugate (ρ : G →* A) (a : A) (g : G) : A := ρ g * a * ρ g⁻¹

def twirl (ρ : G →* A) (a : A) : A := ∫ g, conjugate ρ a g ∂compactHaar

lemma continuous_conjugate
    {G : Type*}
    [contextInstance2861_21 : Group G]
    [contextInstance2861_31 : TopologicalSpace G]
    [contextInstance2861_52 : IsTopologicalGroup G]
    [CompactSpace G]
    [MeasurableSpace G]
    [BorelSpace G]
    {A : Type*}
    [contextInstance2877_21 : NormedRing A]
    [NormedAlgebra ℝ A]
    [CompleteSpace A] (ρ : G →* A) (hρ : Continuous ρ) (a : A) :
    Continuous (conjugate ρ a) :=
  (hρ.mul continuous_const).mul (hρ.comp continuous_inv)

lemma integrable_conjugate (ρ : G →* A) (hρ : Continuous ρ) (a : A) :
    Integrable (conjugate ρ a) compactHaar :=
  continuous_integrable _ (continuous_conjugate ρ hρ a)

lemma conjugate_mul
    {G : Type*}
    [contextInstance2861_21 : Group G]
    [TopologicalSpace G]
    [IsTopologicalGroup G]
    [CompactSpace G]
    [MeasurableSpace G]
    [BorelSpace G]
    {A : Type*}
    [contextInstance2877_21 : NormedRing A]
    [NormedAlgebra ℝ A]
    [CompleteSpace A] (ρ : G →* A) (a : A) (g h : G) :
    conjugate ρ a (g * h) = ρ g * conjugate ρ a h * ρ g⁻¹ := by
  simp only [conjugate, mul_inv_rev, map_mul, mul_assoc]


lemma twirl_commute (ρ : G →* A) (hρ : Continuous ρ) (a : A) (g : G) :
    Commute (ρ g) (twirl ρ a) := by
  have hi := integrable_conjugate ρ hρ a
  have hinv : (ρ g⁻¹) * ρ g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have he : ρ g * twirl ρ a * ρ g⁻¹ = twirl ρ a := by
    rw [twirl, ← integral_const_mul_of_integrable hi]
    rw [← integral_mul_const_of_integrable (hi.const_mul _)]
    simp_rw [← conjugate_mul]
    exact integral_mul_left_eq_self _ g
  have hc := congrArg (fun x : A => x * ρ g) he
  simpa only [Commute, SemiconjBy, mul_assoc, hinv, mul_one] using hc

lemma twirl_trace (τ : A →L[ℝ] ℂ) (hτ : ∀ x y : A, τ (x * y) = τ (y * x))
    (ρ : G →* A) (hρ : Continuous ρ) (a : A) : τ (twirl ρ a) = τ a := by
  rw [twirl, ← τ.integral_comp_comm (integrable_conjugate ρ hρ a)]
  have he (g : G) : τ (conjugate ρ a g) = τ a := by
    rw [conjugate, hτ, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  simp [he, integral_const, measureReal_def]

section Positivity
variable [contextInstance2919_9 : PartialOrder A] [contextInstance2919_26 : IsOrderedAddMonoid A] [contextInstance2919_49 : StarRing A] [contextInstance2919_62 : StarOrderedRing A]
  [contextInstance2920_2 : ClosedIciTopology A] [contextInstance2920_24 : IsOrderedModule ℝ A]

lemma twirl_nonneg
    {G : Type*}
    [contextInstance2861_21 : Group G]
    [contextInstance2861_31 : TopologicalSpace G]
    [contextInstance2861_52 : IsTopologicalGroup G]
    [contextInstance2862_2 : CompactSpace G]
    [contextInstance2862_19 : MeasurableSpace G]
    [contextInstance2862_39 : BorelSpace G]
    {A : Type*}
    [contextInstance2877_21 : NormedRing A]
    [contextInstance2877_36 : NormedAlgebra ℝ A]
    [CompleteSpace A]
    [contextInstance2919_9 : PartialOrder A]
    [contextInstance2919_26 : IsOrderedAddMonoid A]
    [contextInstance2919_49 : StarRing A]
    [contextInstance2919_62 : StarOrderedRing A]
    [contextInstance2920_2 : ClosedIciTopology A]
    [contextInstance2920_24 : IsOrderedModule ℝ A] (ρ : G →* A) (a : A)
    (hρ : ∀ g, ρ g⁻¹ = star (ρ g)) (ha : 0 ≤ a) : 0 ≤ twirl ρ a := by
  apply integral_nonneg
  intro g
  dsimp [conjugate]
  rw [hρ]
  exact star_right_conjugate_nonneg ha _
end Positivity

end SpinAngle.CompactTwirl

namespace SpinAngle
open scoped Matrix.Norms.L2Operator


lemma unitaryGroup_compactSpace (n : Type*) [Fintype n] [DecidableEq n] [Nonempty n] :
    CompactSpace (Matrix.unitaryGroup n ℂ) := by
  apply isCompact_iff_compactSpace.mp
  apply (isCompact_closedBall (0 : Matrix n n ℂ) 1).of_isClosed_subset isClosed_unitary
  intro a ha
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (CStarRing.norm_coe_unitary (⟨a, ha⟩ : unitary (Matrix n n ℂ))).le

end SpinAngle

namespace SpinAngle.CompactTwirl
variable {G : Type*} [contextInstance2949_21 : Group G] [contextInstance2949_31 : TopologicalSpace G] [contextInstance2949_52 : IsTopologicalGroup G]
  [contextInstance2950_2 : CompactSpace G] [contextInstance2950_19 : MeasurableSpace G] [contextInstance2950_39 : BorelSpace G]
variable {E : Type*} [contextInstance2951_21 : NormedAddCommGroup E] [contextInstance2951_44 : InnerProductSpace ℂ E]
  [contextInstance2952_2 : FiniteDimensional ℂ E]


def continuousAction (ρ : Representation ℂ G E) : G →* (E →L[ℂ] E) :=
  (Module.End.toContinuousLinearMap (𝕜 := ℂ) E).toMonoidHom.comp ρ

@[simp] lemma continuousAction_apply
    {G : Type*}
    [contextInstance2949_21 : Group G]
    [TopologicalSpace G]
    [IsTopologicalGroup G]
    [CompactSpace G]
    [MeasurableSpace G]
    [BorelSpace G]
    {E : Type*}
    [contextInstance2951_21 : NormedAddCommGroup E]
    [contextInstance2951_44 : InnerProductSpace ℂ E]
    [contextInstance2952_2 : FiniteDimensional ℂ E] (ρ : Representation ℂ G E) (g : G) (v : E) :
    continuousAction ρ g v = ρ g v := rfl

def operatorTrace : (E →L[ℂ] E) →L[ℂ] ℂ :=
  ((LinearMap.trace ℂ E).comp
    (Module.End.toContinuousLinearMap (𝕜 := ℂ) E).symm.toLinearMap).toContinuousLinearMap

@[simp] lemma operatorTrace_apply
    {G : Type*}
    [Group G]
    [TopologicalSpace G]
    [IsTopologicalGroup G]
    [CompactSpace G]
    [MeasurableSpace G]
    [BorelSpace G]
    {E : Type*}
    [contextInstance2951_21 : NormedAddCommGroup E]
    [contextInstance2951_44 : InnerProductSpace ℂ E]
    [contextInstance2952_2 : FiniteDimensional ℂ E] (a : E →L[ℂ] E) :
    operatorTrace a = LinearMap.trace ℂ E a.toLinearMap := rfl

lemma operatorTrace_mul_comm
    {G : Type*}
    [Group G]
    [TopologicalSpace G]
    [IsTopologicalGroup G]
    [CompactSpace G]
    [MeasurableSpace G]
    [BorelSpace G]
    {E : Type*}
    [contextInstance2951_21 : NormedAddCommGroup E]
    [contextInstance2951_44 : InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (a b : E →L[ℂ] E) :
    operatorTrace (a * b) = operatorTrace (b * a) :=
  LinearMap.trace_mul_comm ℂ a.toLinearMap b.toLinearMap



theorem twirl_irreducible (ρ : Representation ℂ G E) [ρ.IsIrreducible]
    (hρ : Continuous (continuousAction ρ)) (a : E →L[ℂ] E) :
    twirl (continuousAction ρ) a =
      (operatorTrace a / (Module.finrank ℂ E : ℂ)) • (1 : E →L[ℂ] E) := by
  let t := twirl (continuousAction ρ) a
  let f : ρ.IntertwiningMap ρ :=
    t.toLinearMap.intertwiningMap_of_isIntertwiningMap ρ ρ (by
      intro g v
      have h := twirl_commute (continuousAction ρ) hρ a g
      exact (congrArg (fun L : E →L[ℂ] E => L v) h.eq).symm)
  obtain ⟨z, hz⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed (ρ := ρ)).surjective f
  have ht : t = z • (1 : E →L[ℂ] E) := by
    ext v
    exact (congrArg (fun L : ρ.IntertwiningMap ρ => L v) hz).symm
  have htr : operatorTrace t = operatorTrace a :=
    twirl_trace (operatorTrace.restrictScalars ℝ) (operatorTrace_mul_comm (G := G))
      (continuousAction ρ) hρ a
  let : Nontrivial E := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
  have hn : (Module.finrank ℂ E : ℂ) ≠ 0 := by
    exact_mod_cast Module.finrank_pos.ne'
  have hz' : z = operatorTrace a / (Module.finrank ℂ E : ℂ) := by
    apply (eq_div_iff hn).mpr
    rw [ht, map_smul] at htr
    simpa [operatorTrace_apply (G := G), LinearMap.trace_one] using htr
  simpa only [hz'] using ht

end SpinAngle.CompactTwirl



namespace SpinAngle.CompactTwirl
open scoped InnerProductSpace ComplexOrder
variable {G : Type*} [contextInstance3008_21 : Group G] [contextInstance3008_31 : TopologicalSpace G] [contextInstance3008_52 : IsTopologicalGroup G]
  [contextInstance3009_2 : CompactSpace G] [contextInstance3009_19 : MeasurableSpace G] [contextInstance3009_39 : BorelSpace G]
variable {E F : Type*} [contextInstance3010_23 : NormedAddCommGroup E] [contextInstance3010_46 : InnerProductSpace ℂ E]
  [contextInstance3011_2 : NormedAddCommGroup F] [contextInstance3011_25 : InnerProductSpace ℂ F]
  [contextInstance3012_2 : FiniteDimensional ℂ E] [contextInstance3012_26 : FiniteDimensional ℂ F]

lemma twirl_natural (ρ : Representation ℂ G E) (σ : Representation ℂ G F)
    (hρ : Continuous (continuousAction ρ)) (hσ : Continuous (continuousAction σ))
    (a : E →L[ℂ] E) (A : F →L[ℂ] F) (L : ρ.IntertwiningMap σ)
    (hnat : ∀ x, A (L x) = L (a x)) (x : E) :
    twirl (continuousAction σ) A (L x) = L (twirl (continuousAction ρ) a x) := by
  have hi := integrable_conjugate (continuousAction ρ) hρ a
  have hI := integrable_conjugate (continuousAction σ) hσ A
  rw [twirl, ContinuousLinearMap.integral_apply hI, twirl, ContinuousLinearMap.integral_apply hi]
  change _ = L.toLinearMap.toContinuousLinearMap (∫ g, conjugate (continuousAction ρ) a g x ∂compactHaar)
  rw [← ContinuousLinearMap.integral_comp_comm _ (hi.apply_continuousLinearMap x)]
  apply integral_congr_ae
  filter_upwards [] with g
  change σ g (A (σ g⁻¹ (L x))) = L (ρ g (a (ρ g⁻¹ x)))
  rw [← L.isIntertwining, hnat, L.isIntertwining]

lemma continuousAction_inverse_star
    {G : Type*}
    [contextInstance3008_21 : Group G]
    [TopologicalSpace G]
    [IsTopologicalGroup G]
    [CompactSpace G]
    [MeasurableSpace G]
    [BorelSpace G]
    {E : Type*}
    [contextInstance3010_23 : NormedAddCommGroup E]
    [contextInstance3010_46 : InnerProductSpace ℂ E]
    [contextInstance3012_2 : FiniteDimensional ℂ E] (ρ : Representation ℂ G E)
    (hρ : ∀ g x y, ⟪ρ g x,ρ g y⟫_ℂ = ⟪x,y⟫_ℂ) (g : G) :
    continuousAction ρ g⁻¹ = star (continuousAction ρ g) := by
  ext x
  apply ext_inner_left ℂ
  intro y
  change ⟪y,ρ g⁻¹ x⟫_ℂ = ⟪y,(continuousAction ρ g).adjoint x⟫_ℂ
  rw [ContinuousLinearMap.adjoint_inner_right]
  simpa only [inv_inv, continuousAction_apply] using (UnitaryNaturality.inner_move ρ hρ g⁻¹ y x)

end SpinAngle.CompactTwirl

namespace SpinAngle.ProjectionOrder
variable {A : Type*} [contextInstance3043_21 : CStarAlgebra A] [contextInstance3043_38 : PartialOrder A] [contextInstance3043_55 : StarOrderedRing A]
  [contextInstance3044_2 : NonnegSpectrumClass ℝ A]

lemma scalar_projection_le (T P : A) (hT : 0 ≤ T) (hP : IsStarProjection P)
    (c : ℝ) (he : T * P = c • P) : c • P ≤ T := by
  have hstar := congrArg star he
  have hpT : P * T = c • P := by
    simpa only [star_mul, hP.isSelfAdjoint.star_eq, (IsSelfAdjoint.of_nonneg hT).star_eq,
      star_smul, star_trivial] using hstar
  have hc : Commute (1-P) T := by
    dsimp [Commute,SemiconjBy]
    rw [sub_mul,mul_sub,one_mul,mul_one,hpT,he]
  have hn := hc.mul_nonneg (sub_nonneg.mpr hP.le_one) hT
  rw [sub_mul,one_mul,hpT] at hn
  exact sub_nonneg.mp hn
end SpinAngle.ProjectionOrder

namespace SpinAngle.CompactTwirl
open scoped InnerProductSpace ComplexOrder
variable {G : Type*} [contextInstance3062_21 : Group G] [contextInstance3062_31 : TopologicalSpace G] [contextInstance3062_52 : IsTopologicalGroup G]
  [contextInstance3063_2 : CompactSpace G] [contextInstance3063_19 : MeasurableSpace G] [contextInstance3063_39 : BorelSpace G]
variable {E F : Type*} [contextInstance3064_23 : NormedAddCommGroup E] [contextInstance3064_46 : InnerProductSpace ℂ E]
  [contextInstance3065_2 : NormedAddCommGroup F] [contextInstance3065_25 : InnerProductSpace ℂ F]
  [contextInstance3066_2 : FiniteDimensional ℂ E] [contextInstance3066_26 : FiniteDimensional ℂ F]

lemma isotypic_twirl_scalar (ρ : Representation ℂ G E) [ρ.IsIrreducible]
    (σ : Representation ℂ G F)
    (hρ : Continuous (continuousAction ρ)) (hσ : Continuous (continuousAction σ))
    (a : E →L[ℂ] E) (A : F →L[ℂ] F)
    (hnat : ∀ L : ρ.IntertwiningMap σ, ∀ x, A (L x) = L (a x)) :
    twirl (continuousAction σ) A * Isotypic.projection ρ σ =
      (operatorTrace a / (Module.finrank ℂ E : ℂ)) • Isotypic.projection ρ σ := by
  ext v
  apply Isotypic.scalar_on_space ρ σ
    (twirl (continuousAction σ) A).toLinearMap
    (operatorTrace a / (Module.finrank ℂ E : ℂ))
  · intro L x
    change twirl (continuousAction σ) A (L x) = _
    rw [twirl_natural ρ σ hρ hσ a A L (hnat L), twirl_irreducible ρ hρ a]
    simp only [smul_apply, one_apply_eq_self, map_smul]
  · exact (Isotypic.space ρ σ).toSubmodule.starProjection_apply_mem v


lemma isotypic_twirl_lower (ρ : Representation ℂ G E) [ρ.IsIrreducible]
    (σ : Representation ℂ G F)
    (hρ : Continuous (continuousAction ρ)) (hσ : Continuous (continuousAction σ))
    (hσunit : ∀ g x y, ⟪σ g x,σ g y⟫_ℂ = ⟪x,y⟫_ℂ)
    (a : E →L[ℂ] E) (A : F →L[ℂ] F) (ha : 0 ≤ a) (hA : 0 ≤ A)
    (hnat : ∀ L : ρ.IntertwiningMap σ, ∀ x, A (L x) = L (a x)) :
    ((operatorTrace a).re / (Module.finrank ℂ E : ℝ)) • Isotypic.projection ρ σ ≤
      twirl (continuousAction σ) A := by
  apply ProjectionOrder.scalar_projection_le _ _
    (twirl_nonneg _ A (continuousAction_inverse_star σ hσunit) hA)
    (isStarProjection_starProjection (U := (Isotypic.space ρ σ).toSubmodule))
  have ht : operatorTrace a = ((operatorTrace a).re : ℂ) :=
    Complex.eq_re_of_ofReal_le (LinearMap.IsPositive.trace_nonneg
      ((ContinuousLinearMap.nonneg_iff_isPositive).mp ha))
  have h := isotypic_twirl_scalar ρ σ hρ hσ a A hnat
  rw [ht] at h
  convert h using 1 <;> simp only [Isotypic.projection,
    RCLike.real_smul_eq_coe_smul (K := ℂ)]
  congr 1
  change (((operatorTrace a).re / (Module.finrank ℂ E : ℝ) : ℝ) : ℂ) = _
  simp only [Complex.ofReal_div, Complex.ofReal_natCast]

end SpinAngle.CompactTwirl






noncomputable section
open scoped BigOperators
open Set
namespace SpinAngle.CompactMixture
variable {E : Type*} [contextInstance3119_21 : NormedAddCommGroup E] [contextInstance3119_44 : NormedSpace ℝ E] [contextInstance3119_62 : FiniteDimensional ℝ E]

lemma convexHull_compact {s : Set E} (hs : IsCompact s) : IsCompact (convexHull ℝ s) := by
  classical
  let : CompactSpace s := isCompact_iff_compactSpace.mp hs
  let C (k : ℕ) := (Convexity.StdSimplex ℝ (Fin k)) × (Fin k → s)
  let f (k : ℕ) (v : C k) : E := ∑ i, v.1.weights i • (v.2 i).val
  have hf (k : ℕ) : Continuous (f k) := by
    change Continuous (fun v : (Convexity.StdSimplex ℝ (Fin k)) × (Fin k → s) =>
      ∑ i, v.1.weights i • (v.2 i).val)
    apply continuous_finsetSum
    intro i hi
    exact ((Convexity.StdSimplex.continuous_weights_apply ℝ i).comp continuous_fst).smul
      (continuous_subtype_val.comp ((continuous_apply i).comp continuous_snd))
  have hc : IsCompact (⋃ k : Fin (Module.finrank ℝ E + 2), Set.range (f k.val)) :=
    isCompact_iUnion (fun k => isCompact_range (hf k.val))
  convert hc using 1
  ext x
  constructor
  · intro hx
    let t := Caratheodory.minCardFinsetOfMemConvexHull hx
    have ht : (t : Set E) ⊆ s := Caratheodory.minCardFinsetOfMemConvexHull_subseteq hx
    have hm : x ∈ convexHull ℝ (t : Set E) := Caratheodory.mem_minCardFinsetOfMemConvexHull hx
    have hi : AffineIndependent ℝ ((↑) : t → E) :=
      Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull hx
    have hn : Fintype.card t ≤ Module.finrank ℝ E + 1 :=
      hi.card_le_finrank_succ.trans (Nat.add_le_add_right (Submodule.finrank_le _) 1)
    let k : Fin (Module.finrank ℝ E + 2) := ⟨Fintype.card t, by omega⟩
    let e := (Fintype.equivFin t).symm
    obtain ⟨w,hw,hws,hxw⟩ := Finset.mem_convexHull'.mp hm
    let z : Fin k.val → s := fun i => ⟨(e i).val, ht (e i).property⟩
    have hsum : ∑ i : Fin k.val, w (e i).val = 1 := by
      rw [show (∑ i : Fin k.val, w (e i).val) = ∑ j : t, w j.val from
        e.sum_comp (fun j : t => w j.val)]
      simpa only [Finset.sum_coe_sort] using hws
    let v : C k.val := (⟨Finsupp.equivFunOnFinite.symm (fun i => w (e i).val),
      fun i => by simpa using hw _ (e i).property,
      by simpa [Finsupp.sum_fintype] using hsum⟩, z)
    apply Set.mem_iUnion.mpr
    refine ⟨k,v,?_⟩
    simp only [f, v, z, Finsupp.coe_equivFunOnFinite_symm]
    rw [show (∑ i : Fin k.val, w (e i).val • (e i).val) = ∑ j : t, w j.val • j.val from
      e.sum_comp (fun j : t => w j.val • j.val)]
    exact (Finset.sum_coe_sort t (fun j : E => w j • j)).trans hxw
  · intro hx
    obtain ⟨k,v,rfl⟩ := Set.mem_iUnion.mp hx
    exact mem_convexHull_of_exists_fintype (fun i => v.1.weights i) (fun i => (v.2 i).val)
      v.1.weights_nonneg v.1.total_of_fintype (fun i => (v.2 i).property) rfl
end SpinAngle.CompactMixture

namespace SpinAngle.CompactTwirl
variable {G : Type*} [contextInstance3168_21 : Group G] [contextInstance3168_31 : TopologicalSpace G] [contextInstance3168_52 : IsTopologicalGroup G]
  [contextInstance3169_2 : CompactSpace G] [contextInstance3169_19 : MeasurableSpace G] [contextInstance3169_39 : BorelSpace G]
variable {E : Type*} [contextInstance3170_21 : NormedAddCommGroup E] [contextInstance3170_44 : InnerProductSpace ℂ E]
  [contextInstance3171_2 : FiniteDimensional ℂ E]



lemma twirl_finite_mixture (ρ : Representation ℂ G E)
    (hρ : Continuous (continuousAction ρ)) (a : E →L[ℂ] E) :
    ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℝ) (g : ι → G),
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧
      twirl (continuousAction ρ) a = ∑ i, w i • conjugate (continuousAction ρ) a (g i) := by
  let f := conjugate (continuousAction ρ) a
  have hf : Continuous f := continuous_conjugate _ hρ a
  have hc : IsCompact (Set.range f) := isCompact_range hf
  have hm : twirl (continuousAction ρ) a ∈ convexHull ℝ (Set.range f) :=
    (convex_convexHull ℝ _).integral_mem (CompactMixture.convexHull_compact hc).isClosed
      (Filter.Eventually.of_forall fun g => subset_convexHull ℝ _ (Set.mem_range_self g))
      (integrable_conjugate _ hρ a)
  obtain ⟨ι,hι,w,z,hw,hs,hz,he⟩ := mem_convexHull_iff_exists_fintype.mp hm
  let := hι
  choose g hg using hz
  refine ⟨ι,hι,w,g,hw,hs,?_⟩
  rw [← he]
  apply Finset.sum_congr rfl
  intro i _
  rw [← hg i]
end SpinAngle.CompactTwirl

namespace SpinAngle.SignedCarrier
open scoped Classical TensorProduct BigOperators InnerProductSpace ComplexOrder Matrix.Norms.L2Operator MatrixOrder
open SpinAngle.Young SpinAngle.Specht SignedTensor
variable (a b : YoungDiagram) (q : ℕ) (ha : a.colLen 0 ≤ q) (hb : b.colLen 0 ≤ q)

lemma dimension_eq : dimension a b q ha hb =
    Module.finrank ℂ (PolynomialCarrier.Carrier a q ha) *
      Module.finrank ℂ (PolynomialCarrier.Carrier b q hb) :=
  Module.finrank_tensorProduct

lemma dimension_pos : 0 < dimension a b q ha hb := by
  have : Nontrivial (Carrier a b q ha hb) := IsSimpleModule.nontrivial (MonoidAlgebra ℂ (Group q))
    (rep a b q ha hb).asModule
  exact Module.finrank_pos


theorem dimension_le : dimension a b q ha hb ≤
    (Fintype.card (Cells a) + Fintype.card (Cells b) + 1) ^ (q * (q-1)) := by
  rw [dimension_eq]
  let p := Fintype.card (Cells a) + Fintype.card (Cells b) + 1
  have hA : Module.finrank ℂ (PolynomialCarrier.Carrier a q ha) ≤ p ^ (q*(q-1)/2) :=
    (PolynomialCarrier.ordinary_finrank_le a q ha).trans (Nat.pow_le_pow_left (by dsimp [p]; omega) _)
  have hB : Module.finrank ℂ (PolynomialCarrier.Carrier b q hb) ≤ p ^ (q*(q-1)/2) :=
    (PolynomialCarrier.ordinary_finrank_le b q hb).trans (Nat.pow_le_pow_left (by dsimp [p]; omega) _)
  apply (Nat.mul_le_mul hA hB).trans
  rw [← pow_add]
  have he : q*(q-1)/2 + q*(q-1)/2 = q*(q-1) := by
    have hh := PolyDimension.twice_card_lowerIndex q
    rw [PolyDimension.card_lowerIndex] at hh
    omega
  rw [he]

end SpinAngle.SignedCarrier

namespace SpinAngle.SignedTensor
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {q : ℕ}

def conjugateDensity (g : Group q) (A : Mat q × Mat q) : Mat q × Mat q :=
  (g.1.val * A.1 * star g.1.val, g.2.val * A.2 * star g.2.val)

lemma conjugateDensity_isEvenDensity (g : Group q) (A : Mat q × Mat q) (hA : IsEvenDensity A) :
    IsEvenDensity (conjugateDensity g A) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Matrix.nonneg_iff_posSemidef.mp (star_right_conjugate_nonneg hA.1.nonneg g.1.val)
  · exact Matrix.nonneg_iff_posSemidef.mp (star_right_conjugate_nonneg hA.2.1.nonneg g.2.val)
  · change (g.1.val * A.1 * star g.1.val).trace + (g.2.val * A.2 * star g.2.val).trace = 1
    rw [Matrix.trace_mul_cycle, g.1.property.1, one_mul,
      Matrix.trace_mul_cycle, g.2.property.1, one_mul]
    exact hA.2.2

lemma block_conjugateDensity (g : Group q) (A : Mat q × Mat q) :
    block (conjugateDensity g A) = (blockGroup g).val * block A * (blockGroup g⁻¹).val := by
  change block (((g.1.val,g.2.val) * A) * star (g.1.val,g.2.val)) = _
  rw [map_mul, map_mul, block_star, map_inv]
  rfl

variable {τ : Type*} [contextInstance3254_21 : Fintype τ] [contextInstance3254_33 : DecidableEq τ]
lemma tensor_conjugateDensity (g : Group q) (A : Mat q × Mat q) :
    LinearMap.toContinuousLinearMap (TensorRep.action (ι := τ) (block (conjugateDensity g A))) =
      CompactTwirl.conjugate (CompactTwirl.continuousAction (rep (τ := τ)))
        (LinearMap.toContinuousLinearMap (TensorRep.action (block A))) g := by
  apply ContinuousLinearMap.ext
  intro v
  change TensorRep.action (block (conjugateDensity g A)) v =
    TensorRep.action (blockGroup g).val (TensorRep.action (block A)
      (TensorRep.action (blockGroup g⁻¹).val v))
  rw [block_conjugateDensity, map_mul, map_mul]
  rfl
end SpinAngle.SignedTensor

namespace SpinAngle.SignedTensor
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {q : ℕ}
instance groupMeasurableSpace : MeasurableSpace (Group q) := borel _
instance groupBorelSpace : BorelSpace (Group q) := ⟨rfl⟩
variable [contextInstance3273_9 : Nonempty (Fin q)]
instance groupCompactSpace : CompactSpace (Group q) := by
  let := unitaryGroup_compactSpace (Fin q)
  infer_instance
end SpinAngle.SignedTensor

namespace SpinAngle.SignedCarrier
open scoped Classical TensorProduct BigOperators InnerProductSpace ComplexOrder Matrix.Norms.L2Operator MatrixOrder
open SpinAngle.Young SpinAngle.Specht SignedTensor CompactTwirl
variable (a b : YoungDiagram) (q : ℕ) (ha : a.colLen 0 ≤ q) (hb : b.colLen 0 ≤ q)
variable {τ : Type*} [contextInstance3283_21 : Fintype τ] [contextInstance3283_33 : DecidableEq τ]

lemma projection_isStarProjection : IsStarProjection (typeProjection (τ := τ) a b q ha hb) :=
  isStarProjection_starProjection

variable [contextInstance3288_9 : Nonempty (Fin q)]
lemma twirl_lower (A : Mat q × Mat q) (hA : IsEvenDensity A) :
    ((LinearMap.trace ℂ (Carrier a b q ha hb)
      (hermitianAction a b q ha hb A hA.1.isHermitian hA.2.1.isHermitian)).re /
        (dimension a b q ha hb : ℝ)) • typeProjection (τ := τ) a b q ha hb ≤
    twirl (continuousAction (SignedTensor.rep (q := q) (τ := τ)))
      (LinearMap.toContinuousLinearMap (TensorRep.action (block A))) := by
  exact isotypic_twirl_lower (E := Carrier a b q ha hb) (F := Raw (q := q) (τ := τ))
    (rep a b q ha hb) SignedTensor.rep
    (continuous_rep a b q ha hb) SignedTensor.continuous_rep SignedTensor.rep_unitary
    (LinearMap.toContinuousLinearMap (hermitianAction a b q ha hb A hA.1.isHermitian hA.2.1.isHermitian))
    (LinearMap.toContinuousLinearMap (TensorRep.action (block A)))
    ((ContinuousLinearMap.nonneg_iff_isPositive).mpr
      (hermitianAction_positive a b q ha hb A hA.1 hA.2.1))
    ((ContinuousLinearMap.nonneg_iff_isPositive).mpr
      (TensorRep.action_positive (block A) (block_posSemidef A hA.1 hA.2.1)))
    (fun L x => (intertwiner_hermitian a b q ha hb L A hA.1.isHermitian hA.2.1.isHermitian x).symm)
end SpinAngle.SignedCarrier

noncomputable section
namespace SpinAngle.ProjectionOrder
variable {A : Type*} [contextInstance3309_21 : CStarAlgebra A] [contextInstance3309_38 : PartialOrder A] [contextInstance3309_55 : StarOrderedRing A]

lemma rescale_trace_lower (P B : A) (hP : 0 ≤ P) (F t d : ℝ) (hd : 0 < d)
    (ht : Real.exp (-F) ≤ t) (h : (t / d) • P ≤ B) :
    P ≤ (Real.exp F * d) • B := by
  have hbase : (Real.exp (-F) / d) • P ≤ B :=
    (smul_le_smul_of_nonneg_right (div_le_div_of_nonneg_right ht hd.le) hP).trans h
  have hs := smul_le_smul_of_nonneg_left hbase (mul_pos (Real.exp_pos F) hd).le
  have he : (Real.exp F * d) * (Real.exp (-F) / d) = 1 := by
    rw [← mul_div_assoc, mul_right_comm, mul_div_cancel_right₀ _ hd.ne', ← Real.exp_add]
    simp
  simpa only [smul_smul, he, one_smul] using hs
end SpinAngle.ProjectionOrder

namespace SpinAngle.MatrixBridge
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {n : Type*} [contextInstance3325_21 : Fintype n] [contextInstance3325_33 : DecidableEq n]
lemma inverse_mono (a b : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (h : a ≤ b) :
    (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)).symm a ≤ (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)).symm b := by
  apply sub_nonneg.mp
  rw [← map_sub]
  exact map_nonneg (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)).symm (sub_nonneg.mpr h)
end SpinAngle.MatrixBridge

namespace SpinAngle.SignedCarrier
open scoped Classical TensorProduct BigOperators InnerProductSpace ComplexOrder Matrix.Norms.L2Operator MatrixOrder
open SpinAngle.Young SpinAngle.Specht SignedTensor CompactTwirl
variable (a b : YoungDiagram) (q : ℕ) (ha : a.colLen 0 ≤ q) (hb : b.colLen 0 ≤ q)
variable {τ : Type*} [contextInstance3337_21 : Fintype τ] [contextInstance3337_33 : DecidableEq τ] [contextInstance3337_49 : Nonempty (Fin q)]



theorem exists_density_mixture :
    ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℝ) (R : ι → Mat q × Mat q),
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧ (∀ i, IsEvenDensity (R i)) ∧
      typeProjection (τ := τ) a b q ha hb ≤
        (Real.exp (entropy a b q) * (dimension a b q ha hb : ℝ)) •
          ∑ i, w i • LinearMap.toContinuousLinearMap (TensorRep.action (block (R i))) := by
  obtain ⟨A,hA,htr⟩ := exists_density_trace_lower a b q ha hb
  obtain ⟨ι,hι,w,g,hw,hs,he⟩ := twirl_finite_mixture
    (SignedTensor.rep (q := q) (τ := τ)) SignedTensor.continuous_rep
    (LinearMap.toContinuousLinearMap (TensorRep.action (block A)))
  let := hι
  refine ⟨ι,hι,w,fun i => conjugateDensity (g i) A,hw,hs,
    fun i => conjugateDensity_isEvenDensity (g i) A hA,?_⟩
  have hh := twirl_lower (τ := τ) a b q ha hb A hA
  have hbound := ProjectionOrder.rescale_trace_lower _ _
    (projection_isStarProjection (τ := τ) a b q ha hb).nonneg (entropy a b q)
    _ (dimension a b q ha hb : ℝ) (by exact_mod_cast dimension_pos a b q ha hb) htr hh
  rw [he] at hbound
  simpa only [tensor_conjugateDensity] using hbound
end SpinAngle.SignedCarrier

namespace SpinAngle.MatrixBridge
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {n : Type*} [contextInstance3364_21 : Fintype n] [contextInstance3364_33 : DecidableEq n]
local notation "Φ" => (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ))
lemma inverse_real_smul (r : ℝ) (a : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :
    (Φ).symm (r • a) = r • (Φ).symm a := by
  change (Φ).symm ((r : ℂ) • a) = (r : ℂ) • (Φ).symm a
  exact map_smul (Φ).symm _ _

lemma forward_real_smul (r : ℝ) (a : Matrix n n ℂ) :
    Φ (r • a) = r • Φ a := by
  change Φ ((r : ℂ) • a) = (r : ℂ) • Φ a
  exact map_smul Φ _ _

lemma forward_norm (a : Matrix n n ℂ) : ‖Φ a‖ = ‖a‖ := rfl

lemma inverse_norm (a : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :
    ‖(Φ).symm a‖ = ‖a‖ := by
  rw [← forward_norm, (Φ).apply_symm_apply]

lemma inverse_toContinuous (a : Matrix n n ℂ) :
    (Φ).symm (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin a)) = a := by
  exact (Φ).symm_apply_apply a
end SpinAngle.MatrixBridge


namespace SpinAngle.SignedCarrier
open scoped Classical TensorProduct BigOperators InnerProductSpace ComplexOrder Matrix.Norms.L2Operator MatrixOrder
open SpinAngle.Young SpinAngle.Specht SignedTensor
variable (a b : YoungDiagram) (q : ℕ) (ha : a.colLen 0 ≤ q) (hb : b.colLen 0 ≤ q)
variable {τ : Type*} [contextInstance3392_21 : Fintype τ] [contextInstance3392_33 : DecidableEq τ]

def matrixProjection : Matrix (τ → Spin q) (τ → Spin q) ℂ :=
  (Matrix.toEuclideanCLM (n := τ → Spin q) (𝕜 := ℂ)).symm (typeProjection a b q ha hb)

lemma matrixProjection_isStarProjection : IsStarProjection (matrixProjection (τ := τ) a b q ha hb) := by
  have hp := projection_isStarProjection (τ := τ) a b q ha hb
  constructor
  · change matrixProjection a b q ha hb * matrixProjection a b q ha hb = _
    unfold matrixProjection
    rw [← map_mul, hp.isIdempotentElem.eq]
  · change star (matrixProjection a b q ha hb) = _
    unfold matrixProjection
    have hs := (Matrix.toEuclideanCLM (n := τ → Spin q) (𝕜 := ℂ)).symm.map_star'
      (typeProjection a b q ha hb)
    exact hs.symm.trans (congrArg (Matrix.toEuclideanCLM (n := τ → Spin q) (𝕜 := ℂ)).symm hp.isSelfAdjoint.star_eq)

lemma inverse_action (A : Matrix (Spin q) (Spin q) ℂ) :
    (Matrix.toEuclideanCLM (n := τ → Spin q) (𝕜 := ℂ)).symm
      (LinearMap.toContinuousLinearMap (TensorRep.action A)) = TensorRep.tensor (fun _ : τ => A) :=
  MatrixBridge.inverse_toContinuous _

lemma matrix_density_upper (A : Mat q × Mat q) (hA : IsEvenDensity A) :
    ‖TensorRep.tensor (fun _ : τ => block A) * matrixProjection a b q ha hb‖ ≤
      Real.exp (-entropy a b q) := by
  have h := global_density_upper (τ := τ) a b q ha hb A hA
  rw [← MatrixBridge.inverse_norm] at h
  simpa only [map_mul, inverse_action, matrixProjection] using h

lemma density_projection_commute (A : Mat q × Mat q) (hA : IsEvenDensity A) :
    Commute (LinearMap.toContinuousLinearMap (TensorRep.action (ι := τ) (block A)))
      (typeProjection a b q ha hb) := by
  change _ * _ = _ * _
  apply ContinuousLinearMap.ext
  intro v
  exact (Isotypic.projection_commute_natural (E := Carrier a b q ha hb) (F := Raw (q := q) (τ := τ))
    (rep a b q ha hb) SignedTensor.rep
    (hermitianAction a b q ha hb A hA.1.isHermitian hA.2.1.isHermitian)
    (TensorRep.action (block A))
    (TensorRep.action_positive (block A) (block_posSemidef A hA.1 hA.2.1)).isSymmetric
    (fun L x => (intertwiner_hermitian a b q ha hb L A hA.1.isHermitian hA.2.1.isHermitian x).symm)
    v).symm

lemma matrix_density_commute (A : Mat q × Mat q) (hA : IsEvenDensity A) :
    Commute (TensorRep.tensor (fun _ : τ => block A)) (matrixProjection a b q ha hb) := by
  have h := (density_projection_commute (τ := τ) a b q ha hb A hA).map
    (Matrix.toEuclideanCLM (n := τ → Spin q) (𝕜 := ℂ)).symm
  simpa only [inverse_action, matrixProjection] using h

variable [contextInstance3441_9 : Nonempty (Fin q)]


theorem exists_matrix_density_mixture :
    ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℝ) (R : ι → Mat q × Mat q),
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧ (∀ i, IsEvenDensity (R i)) ∧
      matrixProjection (τ := τ) a b q ha hb ≤
        (Real.exp (entropy a b q) * (dimension a b q ha hb : ℝ)) •
          ∑ i, w i • TensorRep.tensor (fun _ : τ => block (R i)) := by
  obtain ⟨ι,hι,w,R,hw,hs,hR,hdom⟩ := exists_density_mixture (τ := τ) a b q ha hb
  let := hι
  refine ⟨ι,hι,w,R,hw,hs,hR,?_⟩
  have h := MatrixBridge.inverse_mono _ _ hdom
  simpa only [MatrixBridge.inverse_real_smul, map_sum, inverse_action, matrixProjection] using h
end SpinAngle.SignedCarrier

namespace SpinAngle.SignedTensor
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {q : ℕ}
lemma block_add (A B : Mat q × Mat q) : block (A+B) = block A + block B := by
  ext i j
  rcases i with ⟨i,bi⟩; rcases j with ⟨j,bj⟩
  cases bi <;> cases bj <;> simp [block, Matrix.blockDiagonal_apply]

lemma block_real_smul (r : ℝ) (A : Mat q × Mat q) : block (r • A) = r • block A := by
  ext i j
  rcases i with ⟨i,bi⟩; rcases j with ⟨j,bj⟩
  cases bi <;> cases bj <;> simp [block, Matrix.blockDiagonal_apply]

lemma block_zero : block (0 : Mat q × Mat q) = 0 := by
  ext i j
  rcases i with ⟨i,bi⟩; rcases j with ⟨j,bj⟩
  cases bi <;> cases bj <;> simp [block, Matrix.blockDiagonal_apply]

lemma block_sum {ι : Type*} (s : Finset ι) (A : ι → Mat q × Mat q) :
    block (∑ i ∈ s, A i) = ∑ i ∈ s, block (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [block_zero]
  | insert i s hi ih => simp only [Finset.sum_insert hi, block_add, ih]

lemma block_trace (A : Mat q × Mat q) : (block A).trace = A.1.trace + A.2.trace := by
  change (Matrix.blockDiagonal (fun b : Bool => cond b A.2 A.1)).trace = _
  rw [Matrix.trace_blockDiagonal]
  simp [add_comm]

variable {J : Type*} [contextInstance3487_21 : Fintype J]

def evenAverage (A : J → Mat q × Mat q) : Mat q × Mat q :=
  (Fintype.card J : ℝ)⁻¹ • ∑ j, A j

lemma evenAverage_isEvenDensity [Nonempty J] (A : J → Mat q × Mat q)
    (hA : ∀ j, IsEvenDensity (A j)) : IsEvenDensity (evenAverage A) := by
  have hpos : 0 < (Fintype.card J : ℝ) := by exact_mod_cast Fintype.card_pos
  have he (A : Mat q × Mat q) : A.1.trace + A.2.trace = (block A).trace := (block_trace A).symm
  refine ⟨?_,?_,?_⟩
  · apply Matrix.nonneg_iff_posSemidef.mp
    simp only [evenAverage, Prod.smul_fst, Prod.fst_sum]
    exact smul_nonneg (inv_nonneg.mpr hpos.le) (Finset.sum_nonneg fun j _ => (hA j).1.nonneg)
  · apply Matrix.nonneg_iff_posSemidef.mp
    simp only [evenAverage, Prod.smul_snd, Prod.snd_sum]
    exact smul_nonneg (inv_nonneg.mpr hpos.le) (Finset.sum_nonneg fun j _ => (hA j).2.1.nonneg)
  · rw [he]
    unfold evenAverage
    rw [block_real_smul, block_sum, Matrix.trace_smul, Matrix.trace_sum]
    simp only [block_trace, (hA _).2.2, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_eq_mul]
    norm_cast
    exact inv_mul_cancel₀ (by exact_mod_cast hpos.ne')
end SpinAngle.SignedTensor






noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace SpinAngle.MatrixAnalysis
variable {n : Type*} [contextInstance3521_21 : Fintype n] [contextInstance3521_33 : DecidableEq n]
abbrev Mat (n : Type*) := Matrix n n ℂ


def root (a : Mat n) : Mat n := cfc Real.sqrt a

def invRoot (a : Mat n) : Mat n := cfc (fun x : ℝ => (Real.sqrt x)⁻¹) a

def support (a : Mat n) : Mat n := cfc (fun x : ℝ => if x = 0 then 0 else 1) a

lemma root_selfAdjoint (a : Mat n) : IsSelfAdjoint (root a) :=
  cfc_predicate _ _
lemma root_nonneg (a : Mat n) : 0 ≤ root a :=
  cfc_nonneg fun _ _ => Real.sqrt_nonneg _
lemma invRoot_selfAdjoint (a : Mat n) : IsSelfAdjoint (invRoot a) :=
  cfc_predicate _ _
lemma invRoot_nonneg (a : Mat n) : 0 ≤ invRoot a :=
  cfc_nonneg fun _ _ => inv_nonneg.mpr (Real.sqrt_nonneg _)
lemma support_selfAdjoint (a : Mat n) : IsSelfAdjoint (support a) :=
  cfc_predicate _ _

lemma root_mul_self (a : Mat n) (ha : 0 ≤ a) : root a * root a = a := by
  rw [root, ← cfc_mul _ _ _ (Matrix.finite_real_spectrum (A := a) |>.continuousOn _)
    (Matrix.finite_real_spectrum (A := a) |>.continuousOn _)]
  calc
    _ = cfc (fun x : ℝ => x) a := by
      apply cfc_congr
      intro x hx
      exact Real.mul_self_sqrt (spectrum_nonneg_of_nonneg ha hx)
    _ = a := cfc_id' ℝ (ha := .of_nonneg ha)

lemma invRoot_mul_root (a : Mat n) (ha : 0 ≤ a) :
    invRoot a * root a = support a := by
  rw [invRoot, root, ← cfc_mul _ _ _ (Matrix.finite_real_spectrum (A := a) |>.continuousOn _)
    (Matrix.finite_real_spectrum (A := a) |>.continuousOn _)]
  apply cfc_congr
  intro x hx
  by_cases hx0 : x = 0
  · simp [hx0]
  · have hs : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr
      (lt_of_le_of_ne (spectrum_nonneg_of_nonneg ha hx) (Ne.symm hx0)))
    simp [hx0, hs]

lemma support_isStarProjection (a : Mat n) : IsStarProjection (support a) := by
  refine ⟨?_, support_selfAdjoint a⟩
  change support a * support a = support a
  rw [support, ← cfc_mul _ _ _ (Matrix.finite_real_spectrum (A := a) |>.continuousOn _)
    (Matrix.finite_real_spectrum (A := a) |>.continuousOn _)]
  apply cfc_congr
  intro x _
  dsimp only
  split_ifs <;> norm_num

lemma mul_support (a : Mat n) (ha : 0 ≤ a) : a * support a = a := by
  conv_lhs => lhs; rw [← cfc_id' ℝ (a := a)]
  rw [support, ← cfc_mul _ _ _ (Matrix.finite_real_spectrum (A := a) |>.continuousOn _)
    (Matrix.finite_real_spectrum (A := a) |>.continuousOn _)]
  calc
    _ = cfc (fun x : ℝ => x) a := by
      apply cfc_congr
      intro x _
      by_cases hx : x = 0 <;> simp [hx]
    _ = a := cfc_id' ℝ (ha := .of_nonneg ha)

lemma root_mul_support (a : Mat n) : root a * support a = root a := by
  rw [root, support, ← cfc_mul _ _ _ (Matrix.finite_real_spectrum (A := a) |>.continuousOn _)
    (Matrix.finite_real_spectrum (A := a) |>.continuousOn _)]
  apply cfc_congr
  intro x _
  by_cases hx : x = 0 <;> simp [hx]

lemma root_commute {a b : Mat n} (h : Commute a b) : Commute (root a) b :=
  h.cfc_real _
lemma invRoot_commute {a b : Mat n} (h : Commute a b) : Commute (invRoot a) b :=
  h.cfc_real _
lemma support_commute {a b : Mat n} (h : Commute a b) : Commute (support a) b :=
  h.cfc_real _



lemma norm_le_re_trace (a : Mat n) (ha : 0 ≤ a) : ‖a‖ ≤ (Matrix.trace a).re := by
  have hA := Matrix.nonneg_iff_posSemidef.mp ha
  rw [hA.isHermitian.trace_eq_sum_eigenvalues, Complex.re_sum]
  conv_lhs => rw [hA.isHermitian.spectral_theorem]
  simp only [Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
    CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
    Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (by
    exact Finset.sum_nonneg fun i _ => hA.eigenvalues_nonneg i)).mpr
  intro i
  simp only [Function.comp_apply, RCLike.norm_ofReal,
    abs_of_nonneg (hA.eigenvalues_nonneg i)]
  exact Finset.single_le_sum (fun j _ => hA.eigenvalues_nonneg j) (Finset.mem_univ i)

lemma norm_sq_le_re_trace_star_mul_self (a : Mat n) :
    ‖a‖ ^ 2 ≤ (Matrix.trace (star a * a)).re := by
  rw [sq, ← CStarRing.norm_star_mul_self]
  exact norm_le_re_trace _ (star_mul_self_nonneg _)



lemma root_mul_support_of_le_smul (a b : Mat n) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (c : ℝ) (hba : b ≤ c • a) : root b * support a = root b := by
  let e := 1 - support a
  have he : IsStarProjection e := (support_isStarProjection a).one_sub
  have hae : a * e = 0 := by
    dsimp [e]
    rw [mul_sub, mul_one, mul_support a ha, sub_self]
  have hupper : star e * b * e ≤ 0 := by
    have hc := star_left_conjugate_le_conjugate hba e
    simpa only [mul_smul_comm, smul_mul_assoc, mul_assoc, hae, mul_zero, smul_zero] using hc
  have hzero : star e * b * e = 0 :=
    le_antisymm hupper (star_left_conjugate_nonneg hb e)
  have hrootzero : star (root b * e) * (root b * e) = 0 := by
    rw [star_mul, (root_selfAdjoint b).star_eq]
    calc
      (star e * root b) * (root b * e) = star e * (root b * root b) * e := by
        simp only [mul_assoc]
      _ = 0 := by rw [root_mul_self b hb, hzero]
  have h := (CStarRing.star_mul_self_eq_zero_iff _).mp hrootzero
  dsimp [e] at h
  rw [mul_sub, mul_one] at h
  exact (sub_eq_zero.mp h).symm

lemma invRoot_mul_self_mul_invRoot (a : Mat n) (ha : 0 ≤ a) :
    invRoot a * a * invRoot a = support a := by
  have hc : Commute (invRoot a) a := invRoot_commute (Commute.refl a)
  have hr : Commute (root a) (invRoot a) := root_commute hc.symm
  calc
    invRoot a * a * invRoot a = invRoot a * (root a * root a) * invRoot a :=
      congrArg (fun x => invRoot a * x * invRoot a) (root_mul_self a ha).symm
    _ = (invRoot a * root a) * (root a * invRoot a) := by simp only [mul_assoc]
    _ = support a * support a := by rw [hr.eq, invRoot_mul_root a ha]
    _ = support a := (support_isStarProjection a).isIdempotentElem.eq

lemma cell_trace_identity (a b c : Mat n) (ha : 0 ≤ a) (hc : 0 ≤ c) :
    (star (root a * invRoot b * root c) * (root a * invRoot b * root c)).trace =
      (invRoot b * a * invRoot b * c).trace := by
  have he : star (root a * invRoot b * root c) * (root a * invRoot b * root c) =
      root c * (invRoot b * a * invRoot b) * root c := by
    simp only [star_mul, (root_selfAdjoint a).star_eq,
      (root_selfAdjoint c).star_eq, (invRoot_selfAdjoint b).star_eq]
    calc
      root c * (invRoot b * root a) * (root a * invRoot b * root c) =
          root c * (invRoot b * (root a * root a) * invRoot b) * root c := by
            simp only [mul_assoc]
      _ = _ := by rw [root_mul_self a ha]
  rw [he, Matrix.trace_mul_comm (root c * (invRoot b * a * invRoot b)) (root c)]
  rw [← mul_assoc, root_mul_self c hc, Matrix.trace_mul_comm c]

lemma cell_trace_nonneg (a b c : Mat n) (ha : 0 ≤ a) (hc : 0 ≤ c) :
    0 ≤ (invRoot b * a * invRoot b * c).trace := by
  rw [← cell_trace_identity a b c ha hc]
  exact (Matrix.nonneg_iff_posSemidef.mp (star_mul_self_nonneg _)).trace_nonneg


lemma re_trace_nonneg
    {n : Type*}
    [contextInstance3521_21 : Fintype n]
    [DecidableEq n] (a : Mat n) (ha : 0 ≤ a) : 0 ≤ a.trace.re :=
  (Complex.nonneg_iff.mp ((Matrix.nonneg_iff_posSemidef.mp ha).trace_nonneg)).1

lemma re_trace_mono {a b : Mat n} (hab : a ≤ b) : a.trace.re ≤ b.trace.re := by
  have h := re_trace_nonneg (b - a) (sub_nonneg.mpr hab)
  simpa only [Matrix.trace_sub, Complex.sub_re, sub_nonneg] using h



lemma re_trace_projection_mul_le (q b : Mat n) (hq : IsStarProjection q) (hb : 0 ≤ b) :
    (q * b).trace.re ≤ b.trace.re := by
  have h := re_trace_mono (star_left_conjugate_le_conjugate hq.le_one (root b))
  rw [mul_one, (root_selfAdjoint b).star_eq, root_mul_self b hb] at h
  rw [Matrix.trace_mul_comm (root b * q) (root b), ← mul_assoc,
    root_mul_self b hb, Matrix.trace_mul_comm b q] at h
  exact h


lemma cell_norm_sq_le_trace (a b c : Mat n) (ha : 0 ≤ a) (hc : 0 ≤ c) :
    ‖root a * invRoot b * root c‖ ^ 2 ≤
      (invRoot b * a * invRoot b * c).trace.re := by
  have h := norm_sq_le_re_trace_star_mul_self (root a * invRoot b * root c)
  rw [cell_trace_identity a b c ha hc] at h
  exact h

end SpinAngle.MatrixAnalysis

namespace SpinAngle.TensorMatrix
open SpinAngle.MatrixAnalysis
variable {ι n : Type*} [contextInstance3707_23 : Fintype ι] [contextInstance3707_35 : DecidableEq ι] [contextInstance3707_51 : Fintype n] [contextInstance3707_63 : DecidableEq n]


def tensor (a : ι → Mat n) : Mat (ι → n) := fun x y => ∏ i, a i (x i) (y i)

lemma tensor_star
    {ι : Type*} {n : Type*}
    [contextInstance3707_23 : Fintype ι]
    [DecidableEq ι]
    [Fintype n]
    [DecidableEq n] (a : ι → Mat n) :
    tensor (fun i => star (a i)) = star (tensor a) := by
  ext x y
  simp [tensor, Matrix.star_apply]

lemma tensor_mul
    {ι : Type*} {n : Type*}
    [contextInstance3707_23 : Fintype ι]
    [contextInstance3707_35 : DecidableEq ι]
    [contextInstance3707_51 : Fintype n]
    [DecidableEq n] (a b : ι → Mat n) :
    tensor (fun i => a i * b i) = tensor a * tensor b := by
  ext x y
  simp only [tensor, Matrix.mul_apply, ← Finset.prod_mul_distrib]
  symm
  simpa using (Finset.sum_prod_piFinset (ι := ι) Finset.univ
    (fun i j => a i (x i) j * b i j (y i)))

lemma tensor_one
    {ι : Type*} {n : Type*}
    [contextInstance3707_23 : Fintype ι]
    [DecidableEq ι]
    [Fintype n]
    [contextInstance3707_63 : DecidableEq n] : tensor (fun _ : ι => (1 : Mat n)) = 1 := by
  ext x y
  classical
  by_cases h : x = y
  · subst y
    simp [tensor]
  · have hxy : ∃ i, x i ≠ y i := Function.ne_iff.mp h
    obtain ⟨i, hi⟩ := hxy
    simp only [tensor, Matrix.one_apply, ite_eq_right h]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

lemma tensor_trace
    {ι : Type*} {n : Type*}
    [contextInstance3707_23 : Fintype ι]
    [contextInstance3707_35 : DecidableEq ι]
    [contextInstance3707_51 : Fintype n]
    [DecidableEq n] (a : ι → Mat n) :
    (tensor a).trace = ∏ i, (a i).trace := by
  simp only [Matrix.trace, Matrix.diag, tensor]
  simpa using (Finset.sum_prod_piFinset (ι := ι) Finset.univ
    (fun i j => a i j j))

lemma tensor_nonneg (a : ι → Mat n) (ha : ∀ i, 0 ≤ a i) :
    0 ≤ tensor a := by
  have hr : tensor a = star (tensor (fun i => root (a i))) * tensor (fun i => root (a i)) := by
    rw [← tensor_star, ← tensor_mul]
    congr 1
    funext i
    rw [(root_selfAdjoint (a i)).star_eq, root_mul_self _ (ha i)]
  rw [hr]
  exact star_mul_self_nonneg _

lemma tensor_selfAdjoint (a : ι → Mat n) (ha : ∀ i, IsSelfAdjoint (a i)) :
    IsSelfAdjoint (tensor a) := by
  change star (tensor a) = tensor a
  rw [← tensor_star]
  congr 1
  funext i
  exact (ha i).star_eq

lemma tensor_norm_sq_le_trace_product (a : ι → Mat n) :
    ‖tensor a‖ ^ 2 ≤ (∏ i, (star (a i) * a i).trace).re := by
  have h := norm_sq_le_re_trace_star_mul_self (tensor a)
  rw [← tensor_star, ← tensor_mul, tensor_trace] at h
  exact h

lemma tensor_norm_sq_le_re_trace_product (a : ι → Mat n) :
    ‖tensor a‖ ^ 2 ≤ ∏ i, (star (a i) * a i).trace.re := by
  have hreal (i : ι) : (star (a i) * a i).trace = ((star (a i) * a i).trace.re : ℂ) :=
    Complex.eq_re_of_ofReal_le (r := 0)
      (by exact (Matrix.nonneg_iff_posSemidef.mp (star_mul_self_nonneg _)).trace_nonneg)
  calc
    _ ≤ (∏ i, (star (a i) * a i).trace).re := tensor_norm_sq_le_trace_product a
    _ = (∏ i, ((star (a i) * a i).trace.re : ℂ)).re :=
      congrArg Complex.re (Finset.prod_congr rfl fun i _ => hreal i)
    _ = _ := by rw [← Complex.ofReal_prod, Complex.ofReal_re]

lemma tensor_cell_norm_sq_le_product (a b c : ι → Mat n)
    (ha : ∀ i, 0 ≤ a i) (hc : ∀ i, 0 ≤ c i) :
    ‖tensor (fun i => root (a i) * invRoot (b i) * root (c i))‖ ^ 2 ≤
      ∏ i, (invRoot (b i) * a i * invRoot (b i) * c i).trace.re := by
  have h := tensor_norm_sq_le_re_trace_product (fun i => root (a i) * invRoot (b i) * root (c i))
  simpa only [cell_trace_identity _ _ _ (ha _) (hc _)] using h

end SpinAngle.TensorMatrix




noncomputable section
open scoped BigOperators
namespace SpinAngle

def missingCellFactor (m b : ℕ) : ℝ :=
  if b < m then ((m : ℝ) / (m - b : ℕ)) ^ (m - b) else 1

def missingCellProductFactor {ι : Type*} [Fintype ι] (m : ℕ) (b : ι → ℕ) : ℝ :=
  ∏ i, missingCellFactor m (b i)

lemma missingCellFactor_nonneg (m b : ℕ) : 0 ≤ missingCellFactor m b := by
  unfold missingCellFactor
  split_ifs <;> positivity

lemma missingCellFactor_le_exp (m b : ℕ) (hb : b ≤ m) :
    missingCellFactor m b ≤ Real.exp b := by
  unfold missingCellFactor
  split_ifs with h
  · have hk : 0 < m - b := Nat.sub_pos_of_lt h
    have hkR : (0 : ℝ) < (m - b : ℕ) := by exact_mod_cast hk
    have hmR : 0 < (m : ℝ) := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le b) h)
    have hratio : 0 < (m : ℝ) / (m - b : ℕ) := div_pos hmR hkR
    apply (Real.log_le_iff_le_exp (pow_pos hratio _)).mp
    rw [Real.log_pow]
    calc
      (m - b : ℕ) * Real.log ((m : ℝ) / (m - b : ℕ))
        ≤ (m - b : ℕ) * ((m : ℝ) / (m - b : ℕ) - 1) :=
          mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hratio) hkR.le
      _ = (b : ℝ) := by
        rw [mul_sub, mul_div_cancel₀ _ hkR.ne', mul_one, Nat.cast_sub hb]
        ring
  · exact Real.one_le_exp (Nat.cast_nonneg b)

theorem missingCellProduct {ι : Type*} [Fintype ι]
    (m : ℕ) (b : ι → ℕ) (hb : ∀ i, b i ≤ m) :
    missingCellProductFactor m b ≤ Real.exp (∑ i, (b i : ℝ)) := by
  unfold missingCellProductFactor
  calc
    ∏ i, missingCellFactor m (b i) ≤ ∏ i, Real.exp (b i : ℝ) :=
      Finset.prod_le_prod₀ (fun i _ => missingCellFactor_nonneg m (b i))
        (fun i _ => missingCellFactor_le_exp m (b i) (hb i))
    _ = Real.exp (∑ i, (b i : ℝ)) := (Real.exp_sum _ _).symm

end SpinAngle

namespace SpinAngle
open scoped BigOperators
variable {ι : Type*} [contextInstance3841_21 : Fintype ι] [contextInstance3841_33 : DecidableEq ι]


lemma retained_product_le
    {ι : Type*}
    [contextInstance3841_21 : Fintype ι]
    [DecidableEq ι] (t : Finset ι) (z : ι → ℝ)
    (hz : ∀ i, 0 ≤ z i) (hs : ∑ i, z i ≤ Fintype.card ι) :
    ∏ i ∈ t, z i ≤ ((Fintype.card ι : ℝ) / t.card) ^ t.card := by
  by_cases ht : t.Nonempty
  · have hkR : 0 < (t.card : ℝ) := by exact_mod_cast ht.card_pos
    have hmR : 0 < (Fintype.card ι : ℝ) :=
      hkR.trans_le (by exact_mod_cast Finset.card_le_univ t)
    let c : ℝ := Fintype.card ι / t.card
    have hc : 0 < c := div_pos hmR hkR
    have hsum : ∑ i ∈ t, z i ≤ Fintype.card ι :=
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by
        intro i _ _; exact hz i)).trans hs
    have hnorm : ∑ i ∈ t, z i / c ≤ t.card := by
      rw [← Finset.sum_div]
      apply (div_le_iff₀ hc).mpr
      dsimp [c]
      rwa [mul_div_cancel₀ _ hkR.ne']
    have hn : ∏ i ∈ t, z i / c ≤ 1 := calc
      _ ≤ ∏ i ∈ t, Real.exp (z i / c - 1) :=
        Finset.prod_le_prod₀ (fun i _ => div_nonneg (hz i) hc.le) fun i _ => by
          have h := Real.add_one_le_exp (z i / c - 1)
          linarith
      _ = Real.exp (∑ i ∈ t, (z i / c - 1)) := (Real.exp_sum _ _).symm
      _ ≤ Real.exp 0 := by
        apply Real.exp_le_exp.mpr
        rw [Finset.sum_sub_distrib]
        simpa using sub_nonpos.mpr hnorm
      _ = 1 := Real.exp_zero
    rw [Finset.prod_div_distrib, Finset.prod_const] at hn
    exact (div_le_one (pow_pos hc _)).mp hn
  · have he : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
    simp [he]

variable {R C : Type*} [contextInstance3877_23 : Fintype R] [contextInstance3877_35 : DecidableEq R] [contextInstance3877_51 : Fintype C] [contextInstance3877_63 : DecidableEq C]


def occupiedRow (W : Finset (R × C)) (i : R) : Finset C :=
  Finset.univ.filter (fun j => (i, j) ∈ W)

def missingInRow (W : Finset (R × C)) (i : R) : ℕ :=
  Fintype.card C - (occupiedRow W i).card

lemma occupiedRow_card_le
    {R : Type*} {C : Type*}
    [Fintype R]
    [contextInstance3877_35 : DecidableEq R]
    [contextInstance3877_51 : Fintype C]
    [contextInstance3877_63 : DecidableEq C] (W : Finset (R × C)) (i : R) :
    (occupiedRow W i).card ≤ Fintype.card C := Finset.card_le_univ _

lemma missingInRow_le
    {R : Type*} {C : Type*}
    [Fintype R]
    [contextInstance3877_35 : DecidableEq R]
    [contextInstance3877_51 : Fintype C]
    [contextInstance3877_63 : DecidableEq C] (W : Finset (R × C)) (i : R) :
    missingInRow W i ≤ Fintype.card C := Nat.sub_le _ _

lemma retained_factor_eq_missingCellFactor (W : Finset (R × C)) (i : R) :
    ((Fintype.card C : ℝ) / (occupiedRow W i).card) ^ (occupiedRow W i).card =
      missingCellFactor (Fintype.card C) (missingInRow W i) := by
  have hc := occupiedRow_card_le W i
  unfold missingInRow missingCellFactor
  rw [Nat.sub_sub_self hc]
  split_ifs with h
  · rfl
  · have hk : (occupiedRow W i).card = 0 := by omega
    simp [hk]

lemma prod_occupiedRow
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    {R : Type*} {C : Type*}
    [contextInstance3877_23 : Fintype R]
    [contextInstance3877_35 : DecidableEq R]
    [contextInstance3877_51 : Fintype C]
    [contextInstance3877_63 : DecidableEq C] (W : Finset (R × C)) (z : R → C → ℝ) :
    (∏ i, ∏ j ∈ occupiedRow W i, z i j) = ∏ x ∈ W, z x.1 x.2 := by
  simp only [occupiedRow, Finset.prod_filter]
  rw [← Finset.prod_product (f := fun x : R × C => if x ∈ W then z x.1 x.2 else 1)]
  simp only [Finset.univ_product_univ, ← Finset.prod_filter]
  congr 1
  ext x
  simp


lemma board_product_le (W : Finset (R × C)) (z : R → C → ℝ)
    (hz : ∀ i j, 0 ≤ z i j) (hs : ∀ i, ∑ j, z i j ≤ Fintype.card C) :
    (∏ x ∈ W, z x.1 x.2) ≤
      missingCellProductFactor (Fintype.card C) (missingInRow W) := by
  rw [← prod_occupiedRow (ι := R) W z]
  unfold missingCellProductFactor
  apply Finset.prod_le_prod₀
  · intro i _
    exact Finset.prod_nonneg fun j _ => hz i j
  · intro i _
    rw [← retained_factor_eq_missingCellFactor]
    exact retained_product_le (occupiedRow W i) (z i) (hz i) (hs i)

end SpinAngle

namespace SpinAngle.MatrixAnalysis
variable {n C : Type*} [contextInstance3931_23 : Fintype n] [contextInstance3931_35 : DecidableEq n] [contextInstance3931_51 : Fintype C] [contextInstance3931_63 : DecidableEq C]


structure Density (n : Type*) [Fintype n] [DecidableEq n] where
  matrix : Mat n
  nonneg : 0 ≤ matrix
  trace_eq_one : matrix.trace = 1

instance : Coe (Density n) (Mat n) := ⟨Density.matrix⟩

def average (r : C → Density n) : Mat n :=
  (Fintype.card C : ℝ)⁻¹ • ∑ j, (r j).matrix

lemma average_nonneg
    {n : Type*} {C : Type*}
    [contextInstance3931_23 : Fintype n]
    [contextInstance3931_35 : DecidableEq n]
    [contextInstance3931_51 : Fintype C]
    [DecidableEq C] (r : C → Density n) : 0 ≤ average r :=
  smul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Finset.sum_nonneg fun j _ => (r j).nonneg)

lemma sum_eq_smul_average
    {n : Type*} {C : Type*}
    [contextInstance3931_23 : Fintype n]
    [contextInstance3931_35 : DecidableEq n]
    [contextInstance3931_51 : Fintype C]
    [DecidableEq C] [Nonempty C] (r : C → Density n) :
    (∑ j, (r j).matrix) = (Fintype.card C : ℝ) • average r := by
  unfold average
  rw [smul_smul, mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero (α := C)), one_smul]

lemma le_smul_average [Nonempty C] (r : C → Density n) (j : C) :
    (r j).matrix ≤ (Fintype.card C : ℝ) • average r := by
  rw [← sum_eq_smul_average]
  exact Finset.single_le_sum (fun k _ => (r k).nonneg) (Finset.mem_univ j)

lemma support_cell_trace_sum [Nonempty C] (r : C → Density n) (s : Density n) :
    ∑ j, (invRoot (average r) * (r j).matrix * invRoot (average r) * s.matrix).trace.re ≤
      Fintype.card C := by
  have he : (∑ j, invRoot (average r) * (r j).matrix * invRoot (average r) * s.matrix) =
      (Fintype.card C : ℝ) • (support (average r) * s.matrix) := by
    rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum,
      sum_eq_smul_average r, mul_smul_comm, smul_mul_assoc, smul_mul_assoc,
      invRoot_mul_self_mul_invRoot _ (average_nonneg r)]
  have ht := congrArg (fun a : Mat n => a.trace.re) he
  simp only [Matrix.trace_sum, Complex.re_sum, Matrix.trace_smul, Complex.smul_re, smul_eq_mul] at ht
  rw [ht]
  have h := re_trace_projection_mul_le (support (average r)) s.matrix
    (support_isStarProjection _) s.nonneg
  rw [s.trace_eq_one, Complex.one_re] at h
  simpa using mul_le_mul_of_nonneg_left h (Nat.cast_nonneg (Fintype.card C))

end SpinAngle.MatrixAnalysis

namespace SpinAngle
open MatrixAnalysis TensorMatrix
variable {n R C : Type*} [contextInstance3979_25 : Fintype n] [contextInstance3979_37 : DecidableEq n]
  [contextInstance3980_2 : Fintype R] [contextInstance3980_14 : DecidableEq R] [contextInstance3980_30 : Fintype C] [contextInstance3980_42 : DecidableEq C] [contextInstance3980_58 : Nonempty C]



theorem normalized_board_bound (W : Finset (R × C))
    (r : C → Density n) (s : R → Density n) :
    ‖tensor (fun w : W => root (r w.val.2).matrix *
      invRoot (average r) * root (s w.val.1).matrix)‖ ^ 2 ≤
        missingCellProductFactor (Fintype.card C) (missingInRow W) := by
  let z : R → C → ℝ := fun i j =>
    (invRoot (average r) * (r j).matrix * invRoot (average r) * (s i).matrix).trace.re
  have hz : ∀ i j, 0 ≤ z i j := fun i j =>
    (Complex.nonneg_iff.mp (cell_trace_nonneg _ _ _ (r j).nonneg (s i).nonneg)).1
  have hs : ∀ i, ∑ j, z i j ≤ Fintype.card C := fun i => support_cell_trace_sum r (s i)
  calc
    _ ≤ ∏ w : W, z w.val.1 w.val.2 :=
      tensor_cell_norm_sq_le_product _ _ _ (fun w => (r w.val.2).nonneg)
        (fun w => (s w.val.1).nonneg)
    _ = ∏ w ∈ W, z w.1 w.2 :=
      (Finset.prod_subtype W (by intro w; rfl) (fun w => z w.1 w.2)).symm
    _ ≤ _ := board_product_le W z hz hs

end SpinAngle






noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace SpinAngle.DependentTensor
variable {ι : Type*} [contextInstance4012_21 : Fintype ι] [contextInstance4012_33 : DecidableEq ι]
variable {ν : ι → Type*} [contextInstance4013_25 : ∀ i, Fintype (ν i)] [contextInstance4013_46 : ∀ i, DecidableEq (ν i)]

abbrev Mat (n : Type*) := Matrix n n ℂ

def tensor (A : ∀ i, Mat (ν i)) : Mat (∀ i, ν i) := fun x y => ∏ i, A i (x i) (y i)

lemma tensor_star
    {ι : Type*}
    [contextInstance4012_21 : Fintype ι]
    [DecidableEq ι]
    {ν : ι → Type*}
    [∀ i, Fintype (ν i)]
    [∀ i, DecidableEq (ν i)] (A : ∀ i, Mat (ν i)) : tensor (fun i => star (A i)) = star (tensor A) := by
  ext x y
  simp [tensor, Matrix.star_apply]

lemma tensor_mul
    {ι : Type*}
    [contextInstance4012_21 : Fintype ι]
    [contextInstance4012_33 : DecidableEq ι]
    {ν : ι → Type*}
    [contextInstance4013_25 : ∀ i, Fintype (ν i)]
    [∀ i, DecidableEq (ν i)] (A B : ∀ i, Mat (ν i)) : tensor (fun i => A i * B i) = tensor A * tensor B := by
  ext x y
  simp only [tensor, Matrix.mul_apply, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i (j : ν i) => A i (x i) j * B i j (y i)))

lemma tensor_one
    {ι : Type*}
    [contextInstance4012_21 : Fintype ι]
    [DecidableEq ι]
    {ν : ι → Type*}
    [∀ i, Fintype (ν i)]
    [contextInstance4013_46 : ∀ i, DecidableEq (ν i)] : tensor (fun i : ι => (1 : Mat (ν i))) = 1 := by
  ext x y
  classical
  by_cases h : x = y
  · subst y; simp [tensor]
  · obtain ⟨i,hi⟩ := Function.ne_iff.mp h
    simp only [tensor, Matrix.one_apply, ite_eq_right h]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

lemma tensor_nonneg (A : ∀ i, Mat (ν i)) (hA : ∀ i, 0 ≤ A i) : 0 ≤ tensor A := by
  have he : tensor A = star (tensor (fun i => CFC.sqrt (A i))) * tensor (fun i => CFC.sqrt (A i)) := by
    rw [← tensor_star, ← tensor_mul]
    congr 1
    funext i
    rw [(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (A i))).star_eq,
      CFC.sqrt_mul_sqrt_self (A i) (hA i)]
  rw [he]
  exact star_mul_self_nonneg _

lemma tensor_projection (P : ∀ i, Mat (ν i)) (hP : ∀ i, IsStarProjection (P i)) :
    IsStarProjection (tensor P) := by
  constructor
  · change tensor P * tensor P = tensor P
    rw [← tensor_mul]
    congr 1
    funext i
    exact (hP i).isIdempotentElem.eq
  · change star (tensor P) = tensor P
    rw [← tensor_star]
    congr 1
    funext i
    exact (hP i).isSelfAdjoint.star_eq

lemma tensor_sum
    {ι : Type*}
    [contextInstance4012_21 : Fintype ι]
    [contextInstance4012_33 : DecidableEq ι]
    {ν : ι → Type*}
    [∀ i, Fintype (ν i)]
    [∀ i, DecidableEq (ν i)] {κ : ι → Type*} [∀ i, Fintype (κ i)]
    (A : ∀ i, κ i → Mat (ν i)) :
    tensor (fun i => ∑ k, A i k) = ∑ f : ∀ i, κ i, tensor (fun i => A i (f i)) := by
  ext x y
  simp only [tensor, Matrix.sum_apply]
  exact (Fintype.prod_sum (fun i (k : κ i) => A i k (x i) (y i)))

lemma tensor_smul
    {ι : Type*}
    [contextInstance4012_21 : Fintype ι]
    [DecidableEq ι]
    {ν : ι → Type*}
    [∀ i, Fintype (ν i)]
    [∀ i, DecidableEq (ν i)] (w : ι → ℝ) (A : ∀ i, Mat (ν i)) :
    tensor (fun i => w i • A i) = (∏ i, w i) • tensor A := by
  ext x y
  simp only [tensor, Matrix.smul_apply, RCLike.real_smul_eq_coe_smul (K := ℂ), smul_eq_mul,
    Finset.prod_mul_distrib]
  change (∏ i, (w i : ℂ)) * _ = ((∏ i, w i : ℝ) : ℂ) * _
  rw [Complex.ofReal_prod]

lemma tensor_sum_smul {κ : ι → Type*} [∀ i, Fintype (κ i)]
    (w : ∀ i, κ i → ℝ) (A : ∀ i, κ i → Mat (ν i)) :
    tensor (fun i => ∑ k, w i k • A i k) =
      ∑ f : ∀ i, κ i, (∏ i, w i (f i)) • tensor (fun i => A i (f i)) := by
  rw [tensor_sum]
  simp only [tensor_smul]

lemma tensor_mono (A B : ∀ i, Mat (ν i)) (hA : ∀ i, 0 ≤ A i) (hAB : ∀ i, A i ≤ B i) :
    tensor A ≤ tensor B := by
  let M (i : ι) (b : Bool) : Mat (ν i) := if b then B i - A i else A i
  have he (i : ι) : (∑ b : Bool, M i b) = B i := by
    simp [M]
  have hm (i : ι) (b : Bool) : 0 ≤ M i b := by
    cases b
    · exact hA i
    · exact sub_nonneg.mpr (hAB i)
  rw [show B = (fun i => ∑ b : Bool, M i b) by funext i; exact (he i).symm, tensor_sum]
  have h := Finset.single_le_sum (s := (Finset.univ : Finset (ι → Bool)))
    (f := fun f => tensor (fun i => M i (f i)))
    (fun f _ => tensor_nonneg _ (fun i => hm i (f i))) (Finset.mem_univ (fun _ => false))
  exact h
end SpinAngle.DependentTensor

namespace SpinAngle.BlockTensor
open DependentTensor
variable {τ J n : Type*} [contextInstance4107_25 : Fintype τ] [contextInstance4107_37 : DecidableEq τ] [contextInstance4107_53 : Fintype J] [contextInstance4107_65 : DecidableEq J]
  [contextInstance4108_2 : Fintype n] [contextInstance4108_14 : DecidableEq n]
variable (f : τ → J)

abbrev Fiber (j : J) := {i : τ // f i = j}

def splitEquiv : (τ → n) ≃ (∀ j : J, Fiber f j → n) where
  toFun x j i := x i.val
  invFun y i := y (f i) ⟨i,rfl⟩
  left_inv x := rfl
  right_inv y := by
    funext j i
    rcases i with ⟨i,hi⟩
    subst j
    rfl


def tensor (A : ∀ j, Mat (Fiber f j → n)) : Mat (τ → n) :=
  fun x y => DependentTensor.tensor A (splitEquiv f x) (splitEquiv f y)

lemma tensor_mul (A B : ∀ j, Mat (Fiber f j → n)) :
    tensor f (fun j => A j * B j) = tensor f A * tensor f B := by
  change (DependentTensor.tensor (fun j => A j * B j)).submatrix (splitEquiv f) (splitEquiv f) = _
  rw [DependentTensor.tensor_mul]
  exact (Matrix.submatrix_mul_equiv _ _ (splitEquiv f) (splitEquiv f) (splitEquiv f)).symm

lemma tensor_star
    {τ : Type*} {J : Type*} {n : Type*}
    [Fintype τ]
    [DecidableEq τ]
    [contextInstance4107_53 : Fintype J]
    [DecidableEq J]
    [Fintype n]
    [DecidableEq n]
    (f : τ → J) (A : ∀ j, Mat (Fiber f j → n)) :
    tensor f (fun j => star (A j)) = star (tensor f A) := by
  ext x y
  simp [tensor, DependentTensor.tensor, Matrix.star_apply]

lemma tensor_one : tensor f (fun j => (1 : Mat (Fiber f j → n))) = 1 := by
  ext x y
  change DependentTensor.tensor (fun j => (1 : Mat (Fiber f j → n))) _ _ = _
  rw [DependentTensor.tensor_one]
  simp only [Matrix.one_apply, Equiv.apply_eq_iff_eq]

lemma tensor_nonneg (A : ∀ j, Mat (Fiber f j → n)) (hA : ∀ j, 0 ≤ A j) : 0 ≤ tensor f A := by
  exact (Matrix.nonneg_iff_posSemidef.mp (DependentTensor.tensor_nonneg A hA)).submatrix (splitEquiv f) |>.nonneg

lemma tensor_mono (A B : ∀ j, Mat (Fiber f j → n)) (hA : ∀ j, 0 ≤ A j) (hAB : ∀ j, A j ≤ B j) :
    tensor f A ≤ tensor f B := by
  have he := DependentTensor.tensor_mono A B hA hAB
  have hn := (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr he)).submatrix (splitEquiv f) |>.nonneg
  exact sub_nonneg.mp hn

lemma tensor_projection (P : ∀ j, Mat (Fiber f j → n)) (hP : ∀ j, IsStarProjection (P j)) :
    IsStarProjection (tensor f P) := by
  constructor
  · change tensor f P * tensor f P = tensor f P
    rw [← tensor_mul]
    congr 1
    funext j
    exact (hP j).isIdempotentElem.eq
  · change star (tensor f P) = tensor f P
    rw [← tensor_star]
    congr 1
    funext j
    exact (hP j).isSelfAdjoint.star_eq

lemma tensor_sum_smul {κ : J → Type*} [∀ j, Fintype (κ j)]
    (w : ∀ j, κ j → ℝ) (A : ∀ j, κ j → Mat (Fiber f j → n)) :
    tensor f (fun j => ∑ k, w j k • A j k) =
      ∑ k : ∀ j, κ j, (∏ j, w j (k j)) • tensor f (fun j => A j (k j)) := by
  ext x y
  change DependentTensor.tensor (fun j => ∑ k, w j k • A j k) _ _ = _
  rw [DependentTensor.tensor_sum_smul]
  simp only [Matrix.sum_apply, Matrix.smul_apply, tensor]
end SpinAngle.BlockTensor

namespace SpinAngle.BlockTensor
open DependentTensor
variable {τ J n : Type*} [contextInstance4180_25 : Fintype τ] [contextInstance4180_37 : DecidableEq τ] [contextInstance4180_53 : Fintype J] [contextInstance4180_65 : DecidableEq J]
  [contextInstance4181_2 : Fintype n] [contextInstance4181_14 : DecidableEq n]
variable (f : τ → J)

lemma prod_fibers
    {τ : Type*} {J : Type*}
    [contextInstance4180_25 : Fintype τ]
    [DecidableEq τ]
    [contextInstance4180_53 : Fintype J]
    [contextInstance4180_65 : DecidableEq J]
    (f : τ → J) {M : Type*} [CommMonoid M] (a : τ → M) :
    (∏ j : J, ∏ i : Fiber f j, a i.val) = ∏ i, a i := by
  calc
    _ = ∏ z : Sigma (Fiber f), a z.2.val :=
      (Fintype.prod_sigma (fun z : Sigma (Fiber f) => a z.2.val)).symm
    _ = _ := (Equiv.sigmaFiberEquiv f).prod_comp a


lemma tensor_cells
    {τ : Type*} {J : Type*} {n : Type*}
    [contextInstance4180_25 : Fintype τ]
    [contextInstance4180_37 : DecidableEq τ]
    [contextInstance4180_53 : Fintype J]
    [contextInstance4180_65 : DecidableEq J]
    [Fintype n]
    [DecidableEq n]
    (f : τ → J) (A : τ → Mat n) :
    tensor f (fun j => DependentTensor.tensor (fun i : Fiber f j => A i.val)) =
      DependentTensor.tensor A := by
  ext x y
  change (∏ j, ∏ i : Fiber f j, A i.val (x i.val) (y i.val)) = _
  exact prod_fibers f (fun i => A i (x i) (y i))

lemma tensor_commute (A B : ∀ j, Mat (Fiber f j → n))
    (h : ∀ j, Commute (A j) (B j)) : Commute (tensor f A) (tensor f B) := by
  change tensor f A * tensor f B = tensor f B * tensor f A
  rw [← tensor_mul, ← tensor_mul]
  congr 1
  funext j
  exact (h j).eq
end SpinAngle.BlockTensor


namespace SpinAngle.TensorMatrix
open MatrixAnalysis
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {ι n : Type*} [contextInstance4214_23 : Fintype ι] [contextInstance4214_35 : DecidableEq ι] [contextInstance4214_51 : Fintype n] [contextInstance4214_63 : DecidableEq n]

lemma tensor_root_square (A : ι → Mat n) (hA : ∀ i, 0 ≤ A i) :
    tensor (fun i => root (A i)) * tensor (fun i => root (A i)) = tensor A := by
  rw [← tensor_mul]
  congr 1
  funext i
  exact root_mul_self _ (hA i)

lemma tensor_root (A : ι → Mat n) (hA : ∀ i, 0 ≤ A i) :
    tensor (fun i => root (A i)) = root (tensor A) := by
  apply (CFC.mul_self_eq_mul_self_iff _ _
    (tensor_nonneg _ (fun i => root_nonneg (A i))) (root_nonneg _)).mp
  rw [tensor_root_square A hA, root_mul_self _ (tensor_nonneg A hA)]

lemma tensor_invRoot_mul_root (A : ι → Mat n) (hA : ∀ i, 0 ≤ A i) :
    tensor (fun i => invRoot (A i)) * tensor (fun i => root (A i)) =
      tensor (fun i => support (A i)) := by
  rw [← tensor_mul]
  congr 1
  funext i
  exact invRoot_mul_root _ (hA i)

lemma tensor_root_mul_support_of_le_smul (A B : ι → Mat n)
    (hA : ∀ i, 0 ≤ A i) (hB : ∀ i, 0 ≤ B i)
    (c : ℝ) (hAB : ∀ i, A i ≤ c • B i) :
    tensor (fun i => root (A i)) * tensor (fun i => support (B i)) =
      tensor (fun i => root (A i)) := by
  rw [← tensor_mul]
  congr 1
  funext i
  exact root_mul_support_of_le_smul _ _ (hB i) (hA i) c (hAB i)
end SpinAngle.TensorMatrix

namespace SpinAngle
open scoped BigOperators
variable {R C : Type*} [contextInstance4250_23 : Fintype R] [contextInstance4250_35 : DecidableEq R] [contextInstance4250_51 : Fintype C] [contextInstance4250_63 : DecidableEq C]

lemma sum_occupiedRow_card (W : Finset (R × C)) :
    ∑ i, (occupiedRow W i).card = W.card := by
  have he (i : R) : (occupiedRow W i).card = ∑ j : C, if (i,j) ∈ W then 1 else 0 := by
    simp only [occupiedRow, Finset.card_eq_sum_ones, Finset.sum_filter]
  simp only [he]
  rw [← Finset.sum_product (f := fun x : R × C => if x ∈ W then (1 : ℕ) else 0)]
  simp only [Finset.univ_product_univ, ← Finset.sum_filter]
  have he : (Finset.univ.filter fun x : R × C => x ∈ W) = W := by ext x; simp
  rw [he]
  simp

lemma sum_missingInRow (W : Finset (R × C)) :
    ∑ i, missingInRow W i = Fintype.card R * Fintype.card C - W.card := by
  have he : (∑ i, missingInRow W i) + W.card = Fintype.card R * Fintype.card C := by
    rw [← sum_occupiedRow_card W, ← Finset.sum_add_distrib]
    have hi (i : R) : missingInRow W i + (occupiedRow W i).card = Fintype.card C :=
      Nat.sub_add_cancel (occupiedRow_card_le W i)
    simp [hi]
  omega

lemma boardPhi_nonneg (W : Finset (R × C)) :
    0 ≤ missingCellProductFactor (Fintype.card C) (missingInRow W) :=
  Finset.prod_nonneg fun rowIndex _ => missingCellFactor_nonneg _ (missingInRow W rowIndex)

lemma boardPhi_le_exp_holes (W : Finset (R × C)) :
    missingCellProductFactor (Fintype.card C) (missingInRow W) ≤
      Real.exp (Fintype.card R * Fintype.card C - W.card : ℕ) := by
  have h := missingCellProduct (Fintype.card C) (missingInRow W) (missingInRow_le W)
  have hs : (∑ i, (missingInRow W i : ℝ)) =
      (Fintype.card R * Fintype.card C - W.card : ℕ) := by
    exact_mod_cast sum_missingInRow W
  rwa [hs] at h
end SpinAngle


namespace SpinAngle
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open SpinAngle.Young



structure TypeLabel (q : ℕ) where
  even : YoungDiagram
  odd : YoungDiagram
  even_height : even.colLen 0 ≤ q
  odd_height : odd.colLen 0 ≤ q

namespace TypeLabel
variable {q : ℕ}
def size (D : TypeLabel q) : ℕ := Fintype.card (Cells D.even) + Fintype.card (Cells D.odd)
def entropy (D : TypeLabel q) : ℝ := SignedCarrier.entropy D.even D.odd q
def dimension (D : TypeLabel q) : ℕ := SignedCarrier.dimension D.even D.odd q D.even_height D.odd_height

def projection (D : TypeLabel q) (τ : Type*) [Fintype τ] [DecidableEq τ] :
    Matrix (τ → SignedTensor.Spin q) (τ → SignedTensor.Spin q) ℂ :=
  SignedCarrier.matrixProjection D.even D.odd q D.even_height D.odd_height

lemma projection_isStarProjection (D : TypeLabel q) (τ : Type*) [Fintype τ] [DecidableEq τ] :
    IsStarProjection (D.projection τ) :=
  SignedCarrier.matrixProjection_isStarProjection D.even D.odd q D.even_height D.odd_height

lemma dimension_pos (D : TypeLabel q) : 0 < D.dimension :=
  SignedCarrier.dimension_pos D.even D.odd q D.even_height D.odd_height

lemma dimension_le (D : TypeLabel q) : D.dimension ≤ (D.size + 1) ^ (q*(q-1)) :=
  SignedCarrier.dimension_le D.even D.odd q D.even_height D.odd_height

lemma entropy_eq_zero_of_size_zero (D : TypeLabel q) (hD : D.size = 0) : D.entropy = 0 := by
  have hs : ∑ i, SignedCarrier.parts D.even D.odd q i = 0 :=
    (SignedCarrier.sum_parts D.even D.odd q D.even_height D.odd_height).trans hD
  have hi : ∀ i, SignedCarrier.parts D.even D.odd q i = 0 := by
    intro i
    have h := Finset.single_le_sum (s := Finset.univ)
      (fun j _ => Nat.zero_le (SignedCarrier.parts D.even D.odd q j)) (Finset.mem_univ i)
    rw [hs] at h
    exact Nat.eq_zero_of_le_zero h
  simp [entropy, SignedCarrier.entropy, EntropyMonomial.entropy, hi]
end TypeLabel

abbrev EvenDensity (q : ℕ) := {A : SignedTensor.Mat q × SignedTensor.Mat q // SignedTensor.IsEvenDensity A}
namespace EvenDensity
variable {q : ℕ}
def matrix (A : EvenDensity q) : Matrix (SignedTensor.Spin q) (SignedTensor.Spin q) ℂ :=
  SignedTensor.block A.val
lemma nonneg (A : EvenDensity q) : 0 ≤ A.matrix :=
  (SignedTensor.block_posSemidef A.val A.property.1 A.property.2.1).nonneg
lemma trace_eq_one (A : EvenDensity q) : A.matrix.trace = 1 := by
  rw [matrix, SignedTensor.block_trace]
  exact A.property.2.2

def toDensity (A : EvenDensity q) : MatrixAnalysis.Density (SignedTensor.Spin q) :=
  ⟨A.matrix,A.nonneg,A.trace_eq_one⟩

variable {J : Type*} [contextInstance4345_21 : Fintype J] [contextInstance4345_33 : Nonempty J]
def mean (A : J → EvenDensity q) : EvenDensity q :=
  ⟨SignedTensor.evenAverage (fun j => (A j).val),
    SignedTensor.evenAverage_isEvenDensity _ (fun j => (A j).property)⟩
lemma mean_matrix (A : J → EvenDensity q) [DecidableEq J] :
    (mean A).matrix = MatrixAnalysis.average (fun j => (A j).toDensity) := by
  unfold mean matrix SignedTensor.evenAverage
  rw [SignedTensor.block_real_smul, SignedTensor.block_sum]
  rfl
end EvenDensity

namespace TypeLabel
variable {q : ℕ}
variable {τ : Type*} [contextInstance4358_21 : Fintype τ] [contextInstance4358_33 : DecidableEq τ]
lemma density_upper (D : TypeLabel q) (A : EvenDensity q) :
    ‖TensorMatrix.tensor (fun _ : τ => A.matrix) * D.projection τ‖ ≤ Real.exp (-D.entropy) :=
  SignedCarrier.matrix_density_upper D.even D.odd q D.even_height D.odd_height A.val A.property

lemma density_commute (D : TypeLabel q) (A : EvenDensity q) :
    Commute (TensorMatrix.tensor (fun _ : τ => A.matrix)) (D.projection τ) :=
  SignedCarrier.matrix_density_commute D.even D.odd q D.even_height D.odd_height A.val A.property

variable [contextInstance4367_9 : Nonempty (Fin q)]
lemma density_mixture (D : TypeLabel q) :
    ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℝ) (R : ι → EvenDensity q),
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧
      D.projection τ ≤ (Real.exp D.entropy * (D.dimension : ℝ)) •
        ∑ i, w i • TensorMatrix.tensor (fun _ : τ => (R i).matrix) := by
  obtain ⟨ι,hι,w,R,hw,hs,hR,hdom⟩ := SignedCarrier.exists_matrix_density_mixture
    (τ := τ) D.even D.odd q D.even_height D.odd_height
  let := hι
  exact ⟨ι,hι,w,fun i => ⟨R i,hR i⟩,hw,hs,hdom⟩
end TypeLabel

namespace TypeBlocks
universe u
open MatrixAnalysis
variable {q : ℕ}
variable {τ : Type*} {J : Type u} [contextInstance4383_34 : Fintype τ] [contextInstance4383_46 : DecidableEq τ] [contextInstance4383_62 : Fintype J] [contextInstance4383_74 : DecidableEq J]

abbrev Fiber (f : τ → J) (j : J) := BlockTensor.Fiber f j

def projection (f : τ → J) (D : J → TypeLabel q) : Mat (τ → SignedTensor.Spin q) :=
  BlockTensor.tensor f (fun j => (D j).projection (Fiber f j))

def entropy (D : J → TypeLabel q) : ℝ := ∑ j, (D j).entropy
def dimension (D : J → TypeLabel q) : ℕ := ∏ j, (D j).dimension

lemma projection_isStarProjection (f : τ → J) (D : J → TypeLabel q) :
    IsStarProjection (projection f D) :=
  BlockTensor.tensor_projection f _ (fun j => (D j).projection_isStarProjection _)

lemma density_commute (f : τ → J) (D : J → TypeLabel q) (A : EvenDensity q) :
    Commute (TensorMatrix.tensor (fun _ : τ => A.matrix)) (projection f D) := by
  have h := BlockTensor.tensor_commute f
    (fun j => TensorMatrix.tensor (fun _ : Fiber f j => A.matrix))
    (fun j => (D j).projection (Fiber f j)) (fun j => (D j).density_commute A)
  have he : BlockTensor.tensor f (fun j => TensorMatrix.tensor (fun _ : Fiber f j => A.matrix)) =
      TensorMatrix.tensor (fun _ : τ => A.matrix) := by
    ext x y
    change (∏ j : J, ∏ t : Fiber f j, A.matrix (x t.val) (y t.val)) =
      ∏ t : τ, A.matrix (x t) (y t)
    exact BlockTensor.prod_fibers f (fun t => A.matrix (x t) (y t))
  rwa [he] at h

variable [contextInstance4410_9 : Nonempty (Fin q)]


theorem density_mixture (f : τ → J) (D : J → TypeLabel q) :
    ∃ (ι : Type u) (_ : Fintype ι) (w : ι → ℝ) (R : ι → J → EvenDensity q),
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i = Real.exp (entropy D) * (dimension D : ℝ)) ∧
      projection f D ≤ ∑ i, w i • TensorMatrix.tensor (fun t : τ => (R i (f t)).matrix) := by
  classical
  choose κ hκ w R hw hs hdom using (fun j : J => (D j).density_mixture (τ := Fiber f j))
  let : ∀ j, Fintype (κ j) := hκ
  let c (j : J) : ℝ := Real.exp (D j).entropy * (D j).dimension
  let z (j : J) (i : κ j) : ℝ := c j * w j i
  have hz (j : J) (i : κ j) : 0 ≤ z j i :=
    mul_nonneg (mul_nonneg (Real.exp_pos _).le (Nat.cast_nonneg _)) (hw j i)
  have hsum (j : J) : ∑ i, z j i = c j := by
    simp only [z, ← Finset.mul_sum, hs, mul_one]
  have hlocal (j : J) : (D j).projection (Fiber f j) ≤
      ∑ i, z j i • TensorMatrix.tensor (fun _ : Fiber f j => (R j i).matrix) := by
    simpa only [z, c, Finset.smul_sum, smul_smul] using hdom j
  refine ⟨(∀ j, κ j), inferInstance, (fun i => ∏ j, z j (i j)),
    (fun i j => R j (i j)), (fun i => Finset.prod_nonneg fun j _ => hz j (i j)), ?_, ?_⟩
  · rw [← Fintype.prod_sum]
    simp only [hsum, c, Finset.prod_mul_distrib]
    rw [← Real.exp_sum]
    simp only [entropy, dimension, Nat.cast_prod]
  · have h := BlockTensor.tensor_mono f _ _
      (fun j => ((D j).projection_isStarProjection (Fiber f j)).nonneg) hlocal
    rw [BlockTensor.tensor_sum_smul] at h
    have he (i : ∀ j, κ j) : BlockTensor.tensor f
        (fun j => TensorMatrix.tensor (fun _ : Fiber f j => (R j (i j)).matrix)) =
        TensorMatrix.tensor (fun t : τ => (R (f t) (i (f t))).matrix) := by
      ext x y
      change (∏ j : J, ∏ t : Fiber f j, (R j (i j)).matrix (x t.val) (y t.val)) =
        ∏ t : τ, (R (f t) (i (f t))).matrix (x t) (y t)
      calc
        _ = ∏ j : J, ∏ t : Fiber f j, (R (f t.val) (i (f t.val))).matrix (x t.val) (y t.val) := by
          apply Finset.prod_congr rfl
          intro j hj
          apply Finset.prod_congr rfl
          intro t ht
          rw [t.property]
        _ = _ := BlockTensor.prod_fibers f (fun t => (R (f t) (i (f t))).matrix (x t) (y t))
    simpa only [he, projection] using h
end TypeBlocks
end SpinAngle

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
