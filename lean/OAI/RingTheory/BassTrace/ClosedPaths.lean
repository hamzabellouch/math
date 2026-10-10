import OAI.RingTheory.BassTrace.FiniteAverages

namespace OAI

noncomputable section

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral

namespace BassTrace.Paths

open scoped BigOperators

section

variable {G ι : Type*} [Group G] [Fintype ι]

abbrev GroupMatrix := Matrix ι ι (MonoidAlgebra ℂ G)

abbrev ScalarMatrix := Matrix ι ι ℂ

def coefficient (e : GroupMatrix (G := G) (ι := ι)) (s : G) : ScalarMatrix (ι := ι) :=
  fun i j => (e i j).coeff s

def support (e : GroupMatrix (G := G) (ι := ι)) : Finset G := by
  classical
  exact Finset.univ.biUnion fun i => Finset.univ.biUnion fun j => (e i j).coeff.support

omit [Group G] in
lemma mem_support (e : GroupMatrix (G := G) (ι := ι)) (s : G) :
    s ∈ support e ↔ coefficient e s ≠ 0 := by
  classical
  simp only [support, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finsupp.mem_support_iff]
  constructor
  · rintro ⟨i,j,h⟩ he
    exact h (congrFun (congrFun he i) j)
  · intro h
    by_contra he
    apply h
    ext i j
    by_contra hij
    exact he ⟨i,j,hij⟩

omit [Group G] in
lemma entry_support_subset (e : GroupMatrix (G := G) (ι := ι)) (i j : ι) :
    (e i j).coeff.support ⊆ support e := by
  classical
  intro s hs
  simp only [support, Finset.mem_biUnion, Finset.mem_univ, true_and]
  exact ⟨i,j,hs⟩

lemma coefficient_mul (e f : GroupMatrix (G := G) (ι := ι)) (t : G) :
    coefficient (e*f) t = ∑ s ∈ support e, coefficient e s * coefficient f (s⁻¹*t) := by
  classical
  ext i j
  simp only [coefficient, Matrix.mul_apply, MonoidAlgebra.coeff_sum,
    Finsupp.finsetSum_apply, Matrix.sum_apply, MonoidAlgebra.coeff_mul_apply_left,
    Finsupp.sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_subset (entry_support_subset e i k)
  intro s _ hs
  rw [Finsupp.notMem_support_iff.mp hs, zero_mul]

def kernel (e : GroupMatrix (G := G) (ι := ι)) (h k : G) : ScalarMatrix (ι := ι) :=
  coefficient e (h⁻¹*k)

omit [Fintype ι] in
lemma kernel_left_invariant (e : GroupMatrix (G := G) (ι := ι)) (c h k : G) :
    kernel e (c*h) (c*k) = kernel e h k := by
  simp [kernel, mul_assoc]

lemma kernel_row_finite (e : GroupMatrix (G := G) (ι := ι)) (h : G) :
    Function.HasFiniteSupport (kernel e h) := by
  classical
  apply (support e).finite_toSet.image (fun s => h*s) |>.subset
  intro k hk
  refine ⟨h⁻¹*k, (mem_support e _).mpr hk, ?_⟩
  simp

lemma kernel_column_finite (e : GroupMatrix (G := G) (ι := ι)) (k : G) :
    Function.HasFiniteSupport (fun h => kernel e h k) := by
  classical
  apply (support e).finite_toSet.image (fun s => k*s⁻¹) |>.subset
  intro h hh
  refine ⟨h⁻¹*k, (mem_support e _).mpr hh, ?_⟩
  simp

lemma kernel_idempotent (e : GroupMatrix (G := G) (ι := ι)) (he : e*e=e) (h k : G) :
    (∑ s ∈ support e, kernel e h (h*s) * kernel e (h*s) k) = kernel e h k := by
  have hh := coefficient_mul e e (h⁻¹*k)
  rw [he] at hh
  simpa only [kernel, mul_inv_rev, inv_mul_cancel_left, mul_assoc] using hh.symm

lemma kernel_idempotent_finsum (e : GroupMatrix (G := G) (ι := ι)) (he : e*e=e)
    (h k : G) :
    (∑ᶠ u, kernel e h u * kernel e u k) = kernel e h k := by
  classical
  have hs : Function.support (fun u => kernel e h u * kernel e u k) ⊆
      (fun s => h*s) '' (support e : Set G) := by
    intro u hu
    refine ⟨h⁻¹*u, (mem_support e _).mpr ?_, by simp⟩
    intro hz
    exact hu (by change coefficient e (h⁻¹*u) * _ = 0; rw [hz, zero_mul])
  rw [finsum_eq_finsetSum_of_support_subset (f := fun u : G => kernel e h u * kernel e u k) (s := (support e).image (fun s => h*s))
    (by simpa only [Finset.coe_image] using hs)]
  rw [Finset.sum_image (fun a _ b _ hab => mul_left_cancel hab)]
  exact kernel_idempotent e he h k

end

section

variable {G : Type*} [Group G]

def pathSetoid (g : G) (n : ℕ) : Setoid (Fin (n+1) → G) where
  r h k := ∃ c : Subgroup.centralizer ({g} : Set G), ∀ i, (c : G)*h i = k i
  iseqv := ⟨fun h => ⟨1, by simp⟩, by
    rintro h k ⟨c,hc⟩
    refine ⟨c⁻¹, fun i => ?_⟩
    rw [← hc i]
    simp,
    by
    rintro h k l ⟨c,hc⟩ ⟨d,hd⟩
    refine ⟨d*c, fun i => ?_⟩
    change ((d:G)*(c:G))*h i = l i
    rw [mul_assoc,hc,hd]⟩

abbrev Orbit (g : G) (n : ℕ) := Quotient (pathSetoid g n)

def increment (g : G) (n : ℕ) (h : Fin (n+1) → G) (i : Fin (n+1)) : G :=
  (h i)⁻¹ * (if i = Fin.last n then g*h 0 else h (finRotate (n+1) i))

lemma increment_castSucc (g : G) (n : ℕ) (h : Fin (n+1) → G) (i : Fin n) :
    increment g n h i.castSucc = (h i.castSucc)⁻¹*h i.succ := by
  simp [increment,Fin.castSucc_ne_last]

lemma increment_last (g : G) (n : ℕ) (h : Fin (n+1) → G) :
    increment g n h (Fin.last n) = (h (Fin.last n))⁻¹*g*h 0 := by
  simp [increment,mul_assoc]

lemma increment_invariant (g : G) (n : ℕ)
    (c : Subgroup.centralizer ({g} : Set G)) (h : Fin (n+1) → G) :
    increment g n (fun i => c*h i) = increment g n h := by
  funext i
  have hc := Subgroup.mem_centralizer_singleton_iff.mp c.property
  simp only [increment]
  split_ifs
  · rw [← mul_assoc g, ← hc, mul_assoc (c:G)]
    simp [mul_assoc]
  · simp [mul_assoc]

lemma increment_eq_imp_related (g : G) (n : ℕ) (h k : Fin (n+1) → G)
    (he : increment g n h = increment g n k) : pathSetoid g n h k := by
  let c : G := k 0*(h 0)⁻¹
  have hk (i : Fin (n+1)) : k i = c*h i := by
    induction i using Fin.induction with
    | zero => simp [c]
    | succ i hi =>
      have hi' := congrFun he i.castSucc
      rw [increment_castSucc,increment_castSucc,hi] at hi'
      have hm := congrArg (fun z => (c*h i.castSucc)*z) hi'
      simpa [mul_assoc] using hm.symm
  have ht := congrFun he (Fin.last n)
  rw [increment_last,increment_last,hk (Fin.last n),hk 0] at ht
  have hcg := congrArg (fun z => h (Fin.last n)*z*(h 0)⁻¹) ht
  have hc' : g = c⁻¹*g*c := by simpa [mul_inv_rev,mul_assoc] using hcg
  have hc : c*g = g*c := by
    calc c*g = c*(c⁻¹*g*c) := congrArg (c*·) hc'
         _ = g*c := by group
  exact ⟨⟨c,Subgroup.mem_centralizer_singleton_iff.mpr hc⟩,fun i => (hk i).symm⟩

def orbitIncrement (g : G) (n : ℕ) : Orbit g n → (Fin (n+1) → G) :=
  Quotient.lift (increment g n) (by
    rintro h k ⟨c,hc⟩
    have hk : k = fun i => c*h i := funext fun i => (hc i).symm
    rw [hk,increment_invariant])

lemma orbitIncrement_injective (g : G) (n : ℕ) :
    Function.Injective (orbitIncrement g n) := by
  intro q r
  induction q using Quotient.inductionOn with | _ h =>
    induction r using Quotient.inductionOn with | _ k =>
      exact fun he => Quotient.sound (increment_eq_imp_related g n h k he)

variable {ι : Type*} [Fintype ι]

def weight (e : GroupMatrix (G := G) (ι := ι)) (g : G) (n : ℕ)
    (h : Fin (n+1) → G) : ℂ := by
  classical
  exact Matrix.trace (List.ofFn (fun i => coefficient e (increment g n h i))).prod

lemma weight_invariant (e : GroupMatrix (G := G) (ι := ι)) (g : G) (n : ℕ)
    (c : Subgroup.centralizer ({g} : Set G)) (h : Fin (n+1) → G) :
    weight e g n (fun i => c*h i) = weight e g n h := by
  classical
  simp only [weight,increment_invariant]

lemma weight_ne_zero_support (e : GroupMatrix (G := G) (ι := ι)) (g : G) (n : ℕ)
    (h : Fin (n+1) → G) (hw : weight e g n h ≠ 0) (i : Fin (n+1)) :
    increment g n h i ∈ support e := by
  classical
  apply (mem_support e _).mpr
  intro hi
  apply hw
  have hz : (0 : ScalarMatrix (ι := ι)) ∈
      List.ofFn (fun j => coefficient e (increment g n h j)) := by
    exact List.mem_ofFn.mpr ⟨i,hi⟩
  simp only [weight,List.prod_eq_zero hz,Matrix.trace_zero]

def orbitWeight (e : GroupMatrix (G := G) (ι := ι)) (g : G) (n : ℕ) :
    Orbit g n → ℂ := Quotient.lift (weight e g n) (by
  rintro h k ⟨c,hc⟩
  have hk : k = fun i => c*h i := funext fun i => (hc i).symm
  rw [hk,weight_invariant])

lemma orbitWeight_finite (e : GroupMatrix (G := G) (ι := ι)) (g : G) (n : ℕ) :
    Function.HasFiniteSupport (orbitWeight e g n) := by
  classical
  have hfinite : {f : Fin (n+1) → G | ∀ i, f i ∈ support e}.Finite := by
    exact Set.Finite.pi' (fun _ => (support e).finite_toSet)
  apply (hfinite.preimage (orbitIncrement_injective g n).injOn).subset
  intro q hq
  induction q using Quotient.inductionOn with | _ h =>
    exact weight_ne_zero_support e g n h hq

def pathVector (e : GroupMatrix (G := G) (ι := ι)) (g : G) (n : ℕ) :
    Orbit g n →₀ ℂ := Finsupp.ofSupportFinite (orbitWeight e g n) (orbitWeight_finite e g n)

end

section

variable {G : Type*} [Group G]

def twist (g : G) (n : ℕ) (h : Fin (n+1) → G) : Fin (n+1) → G :=
  Fin.snoc (fun i : Fin n => h i.succ) (g*h 0)

@[simp] lemma twist_castSucc (g : G) (n : ℕ) (h : Fin (n+1) → G) (i : Fin n) :
    twist g n h i.castSucc = h i.succ := by simp [twist]

@[simp] lemma twist_last (g : G) (n : ℕ) (h : Fin (n+1) → G) :
    twist g n h (Fin.last n) = g*h 0 := by simp [twist]

lemma rotate_castSucc (n : ℕ) (i : Fin n) :
    finRotate (n+1) i.castSucc = i.succ := finRotate_of_lt i.isLt

lemma increment_twist (g : G) (n : ℕ) (h : Fin (n+1) → G) :
    increment g n (twist g n h) = increment g n h ∘ finRotate (n+1) := by
  funext i
  cases n with
  | zero =>
    have hi : i = Fin.last 0 := Fin.ext (by omega)
    subst i
    simp only [Function.comp_apply,finRotate_last,increment_last,twist_last]
    have hz : (0 : Fin 1) = Fin.last 0 := rfl
    rw [hz,increment_last]
    simp [mul_assoc]
    exact twist_last g 0 h
  | succ n =>
    induction i using Fin.lastCases with
    | last =>
      simp only [increment_last,twist_last,Function.comp_apply,finRotate_last]
      have hz : (0 : Fin (n+1+1)) = (0 : Fin (n+1)).castSucc := rfl
      rw [hz,twist_castSucc,increment_castSucc]
      simp [mul_assoc]
    | cast i =>
      rw [increment_castSucc]
      simp only [Function.comp_apply,rotate_castSucc,twist_castSucc]
      induction i using Fin.lastCases with
      | last =>
        simp only [Fin.succ_last,twist_last,increment_last,mul_assoc]
      | cast i =>
        rw [← Fin.castSucc_succ,twist_castSucc,increment_castSucc]

variable {ι : Type*} [Fintype ι]

lemma weight_twist (e : GroupMatrix (G := G) (ι := ι)) (g : G) (n : ℕ)
    (h : Fin (n+1) → G) : weight e g n (twist g n h) = weight e g n h := by
  classical
  simp only [weight,increment_twist,Function.comp_apply]
  rw [List.ofFn_succ',List.ofFn_succ]
  simp only [rotate_castSucc,finRotate_last,List.prod_concat,List.prod_cons]
  exact Matrix.trace_mul_comm _ _

end

variable {G ι : Type*} [Group G] [Fintype ι]

def prefixProduct (e : GroupMatrix (G := G) (ι := ι)) {n : ℕ}
    (h : Fin (n+1) → G) : ScalarMatrix (ι := ι) := by
  classical
  exact (List.ofFn (fun i : Fin n => kernel e (h i.castSucc) (h i.succ))).prod

lemma weight_eq_prefix (e : GroupMatrix (G := G) (ι := ι)) (g : G) (n : ℕ)
    (h : Fin (n+1) → G) : weight e g n h =
      Matrix.trace (prefixProduct e h * kernel e (h (Fin.last n)) (g*h 0)) := by
  classical
  rw [weight,List.ofFn_succ',List.prod_concat]
  simp only [increment_castSucc,increment_last,prefixProduct,kernel,mul_assoc]

lemma prefixProduct_snoc (e : GroupMatrix (G := G) (ι := ι)) (n : ℕ)
    (h : Fin (n+1) → G) (u : G) :
    prefixProduct e (Fin.snoc h u) = prefixProduct e h * kernel e (h (Fin.last n)) u := by
  classical
  unfold prefixProduct
  rw [List.ofFn_succ',List.prod_concat]
  congr 1
  · congr 2
    funext i
    simp [← Fin.castSucc_succ]
  · simp

lemma weight_snoc (e : GroupMatrix (G := G) (ι := ι)) (g : G) (n : ℕ)
    (h : Fin (n+1) → G) (u : G) : weight e g (n+1) (Fin.snoc h u) =
    Matrix.trace (prefixProduct e h *
      (kernel e (h (Fin.last n)) u * kernel e u (g*h 0))) := by
  classical
  rw [weight_eq_prefix,prefixProduct_snoc]
  have hz : (0 : Fin (n+1+1)) = (0 : Fin (n+1)).castSucc := rfl
  simp only [Fin.snoc_last,mul_assoc,hz,Fin.snoc_castSucc]

lemma weight_snoc_finite (e : GroupMatrix (G := G) (ι := ι)) (g : G) (n : ℕ)
    (h : Fin (n+1) → G) : Function.HasFiniteSupport (fun u => weight e g (n+1) (Fin.snoc h u)) := by
  apply (kernel_row_finite e (h (Fin.last n))).subset
  intro u hu hz
  apply hu
  dsimp only
  rw [weight_snoc,hz,zero_mul,mul_zero,Matrix.trace_zero]

lemma weight_snoc_finsum (e : GroupMatrix (G := G) (ι := ι)) (he : e*e=e)
    (g : G) (n : ℕ) (h : Fin (n+1) → G) :
    (∑ᶠ u : G, weight e g (n+1) (Fin.snoc h u)) = weight e g n h := by
  classical
  let f : ScalarMatrix (ι := ι) →ₗ[ℂ] ℂ :=
    (Matrix.traceLinearMap ι ℂ ℂ).comp (LinearMap.mulLeft ℂ (prefixProduct e h))
  have hs : Function.HasFiniteSupport (fun u =>
      kernel e (h (Fin.last n)) u * kernel e u (g*h 0)) := by
    apply (kernel_row_finite e (h (Fin.last n))).subset
    intro u hu hz
    apply hu
    dsimp only
    rw [hz,zero_mul]
  simp only [weight_snoc]
  rw [weight_eq_prefix]
  change (∑ᶠ u : G, f (kernel e (h (Fin.last n)) u * kernel e u (g*h 0))) = _
  rw [← map_finsum f hs,kernel_idempotent_finsum e he]
  rfl

end BassTrace.Paths

end

end OAI
