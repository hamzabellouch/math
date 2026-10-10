import Mathlib
import OAI.RepresentationTheory.VertexAlgebra.InverseEnergySelf

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

universe u

noncomputable section
open scoped Topology
open Filter
namespace StronglyRationalVOA.SmoothCircleFunction
open scoped ContDiff
theorem coefficient_differentiated (f : SmoothCircleFunction) (k : ℕ) (n : ℤ) :
    (f.differentiated k).coefficient n = (Complex.I*(n : ℂ))^k*f.coefficient n := by
  by_cases hn : n = 0
  · subst n
    cases k with
    | zero => change fourierCoeffOn period_pos (iteratedDeriv 0 f) 0 = _; simp [coefficient]
    | succ k =>
      have h := (f.differentiated k).coefficient_deriv_zero
      have hd : (((f.differentiated k).differentiated 1) : ℝ → ℂ) =
          (f.differentiated (k+1) : ℝ → ℂ) := by
        change iteratedDeriv 1 (iteratedDeriv k f) = iteratedDeriv (k+1) f
        rw [iteratedDeriv_one,iteratedDeriv_succ]
      change fourierCoeffOn period_pos _ 0 = 0 at h
      rw [hd] at h
      simpa only [coefficient,Int.cast_zero,mul_zero,zero_pow k.succ_ne_zero,zero_mul] using h
  · exact (f.coefficient_iteratedDeriv k hn).symm

 
theorem differentiated_support (f : SmoothCircleFunction) (k : ℕ) :
    tsupport (f.differentiated k) ⊆ tsupport f := by
  change tsupport (iteratedDeriv k f) ⊆ tsupport f
  induction k with
  | zero => simp only [iteratedDeriv_zero,Set.Subset.rfl]
  | succ k ih =>
    rw [iteratedDeriv_succ]
    exact tsupport_deriv_subset.trans ih

 
theorem differentiated_mul_zero {f g : SmoothCircleFunction}
    (hfg : Disjoint (tsupport f) (tsupport g)) (k : ℕ) (t : ℝ) :
    f.differentiated k t * g t = 0 := by
  by_cases ht : t ∈ tsupport f
  · have htg : t ∉ tsupport g := fun hg => Set.disjoint_left.mp hfg ht hg
    rw [image_eq_zero_of_notMem_tsupport htg,mul_zero]
  · have htf : t ∉ tsupport (f.differentiated k) := fun hk => ht (f.differentiated_support k hk)
    rw [image_eq_zero_of_notMem_tsupport htf,zero_mul]

 

theorem hasSum_weighted_convolution_zero {f g : SmoothCircleFunction}
    (hfg : Disjoint (tsupport f) (tsupport g)) (k : ℕ) (n : ℤ) :
    HasSum (fun m : ℤ => (m : ℂ)^k*f.coefficient m*g.coefficient (n-m)) 0 := by
  have H := (f.differentiated k).coefficient_mul g n
  have hz : ((f.differentiated k).mul g).coefficient n = 0 := by
    unfold coefficient
    have he : (((f.differentiated k).mul g) : ℝ → ℂ) = 0 :=
      funext (f.differentiated_mul_zero hfg k)
    rw [he,fourierCoeffOn_eq_integral]
    simp
  rw [hz] at H
  simp only [coefficient_differentiated,mul_pow,mul_assoc] at H
  have HI := H.mul_left ((Complex.I^k)⁻¹)
  simpa only [mul_zero,← mul_assoc,inv_mul_cancel₀ (pow_ne_zero _ Complex.I_ne_zero),one_mul] using HI

end StronglyRationalVOA.SmoothCircleFunction

namespace StronglyRationalVOA.SmoothCircleFunction

 
theorem hasSum_polynomial_convolution_zero {f g : SmoothCircleFunction}
    (hfg : Disjoint (tsupport f) (tsupport g)) (P : Polynomial ℂ) (n : ℤ) :
    HasSum (fun m : ℤ => P.eval (m : ℂ)*f.coefficient m*g.coefficient (n-m)) 0 := by
  classical
  have H : HasSum (fun m : ℤ => ∑ k ∈ P.support,
      P.coeff k * ((m : ℂ)^k*f.coefficient m*g.coefficient (n-m))) 0 := by
    simpa only [mul_zero,Finset.sum_const_zero] using
      (hasSum_sum (s := P.support) (fun k _ =>
        (hasSum_weighted_convolution_zero hfg k n).mul_left (P.coeff k)))
  have he (m : ℤ) : P.eval (m : ℂ)*f.coefficient m*g.coefficient (n-m) =
      ∑ k ∈ P.support, P.coeff k*((m : ℂ)^k*f.coefficient m*g.coefficient (n-m)) := by
    rw [Polynomial.eval_eq_sum,Polynomial.sum_def,Finset.sum_mul,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    ring
  simpa only [he] using H

 

theorem hasSum_choose_convolution_zero {f g : SmoothCircleFunction}
    (hfg : Disjoint (tsupport f) (tsupport g)) (c : ℂ) (j : ℕ) (n : ℤ) :
    HasSum (fun m : ℤ => Ring.choose ((m : ℂ)+c) j * f.coefficient m*g.coefficient (n-m)) 0 := by
  let P : Polynomial ℂ := Polynomial.C ((j.factorial : ℂ)⁻¹) *
    ((descPochhammer ℤ j).map (Int.castRingHom ℂ)).comp (Polynomial.X+Polynomial.C c)
  have he (m : ℤ) : P.eval (m : ℂ) = Ring.choose ((m : ℂ)+c) j := by
    dsimp only [P]
    rw [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_comp,
      Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C,Polynomial.eval_map,
      Ring.choose_eq_smul]
    have hh : Int.castRingHom ℂ = (RingHom.smulOneHom : ℤ →+* ℂ) := by
      ext i
      simp only [RingHom.smulOneHom_apply,zsmul_eq_mul,mul_one]
      rfl
    rw [hh,Polynomial.eval₂_smulOneHom_eq_smeval,smul_eq_mul]
  simpa only [he] using hasSum_polynomial_convolution_zero hfg P n

end StronglyRationalVOA.SmoothCircleFunction

namespace StronglyRationalVOA.CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  (A : CFTTypeVOA V)

 
theorem physicalMode_energy_eigenvalue {d e : ℕ} {a x : V}
    (ha : a ∈ A.grade d) (hx : x ∈ A.grade e) (m : ℤ) :
    A.virasoroMode 0 (A.physicalMode a d m x) =
      ((e : ℂ)-m) • A.physicalMode a d m x := by
  rw [physicalMode,A.mode_energy_eigenvalue ha hx]
  congr 1
  push_cast
  ring

 

theorem physicalMode_commutator_finite {a b : V} {d e : ℕ}
    (ha : a ∈ A.grade d) (hb : b ∈ A.grade e) (m n : ℤ) (y : V) :
    A.physicalMode a d m (A.physicalMode b e n y)-
      A.physicalMode b e n (A.physicalMode a d m y) =
    ∑ j ∈ Finset.range (d+e), Ring.choose ((m : ℂ)+d-1) j •
      mode A.fields (mode A.fields a j b) (m+n+d+e-2-j) y := by
  simp only [physicalMode]
  rw [A.toVertexAlgebra.mode_commutator]
  have hi (j : ℕ) : (m+(d : ℤ)-1)+(n+e-1)-j = m+n+d+e-2-j := by omega
  simp only [hi,Int.cast_sub,Int.cast_add,Int.cast_natCast,Int.cast_one]
  apply finsum_eq_sum_of_support_subset
  intro j hj
  simp only [Finset.coe_range,Set.mem_Iio]
  by_contra h
  apply hj
  have hz := A.mode_eq_zero_of_negative_energy ha hb (j : ℤ) (by omega)
  simp only [hz,mode_zero,LinearMap.zero_apply,smul_zero]

namespace UnitaryStructure
variable {A} (U : A.UnitaryStructure)

include U in
 

theorem physicalMode_cross_orthogonal {a b x y : V} {d e D E : ℕ}
    (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    (hx : x ∈ A.grade D) (hy : y ∈ A.grade E) (m n : ℤ)
    (hne : n ≠ m+(E : ℤ)-D) :
    inner ℂ (A.physicalMode a d m x) (A.physicalMode b e n y) = 0 := by
  have h := U.virasoro_adjoint 0 (A.physicalMode a d m x) (A.physicalMode b e n y)
  simp only [neg_zero,A.physicalMode_energy_eigenvalue ha hx,
    A.physicalMode_energy_eigenvalue hb hy,inner_smul_left,inner_smul_right,
    map_sub,map_natCast,map_intCast] at h
  have hc : ((D : ℂ)-m)-((E : ℂ)-n) ≠ 0 := by
    intro hz
    apply hne
    have heq : (n : ℂ) = (m : ℂ)+E-D := by linear_combination hz
    exact_mod_cast heq
  apply (mul_eq_zero.mp (show (((D : ℂ)-m)-((E : ℂ)-n))*
      inner ℂ (A.physicalMode a d m x) (A.physicalMode b e n y) = 0 from ?_)).resolve_left hc
  rw [sub_mul,h,sub_self]

end UnitaryStructure
end StronglyRationalVOA.CFTTypeVOA

namespace StronglyRationalVOA

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

 

theorem summable_inner_diagonal {u v : ℤ → H}
    (hu : Summable (fun n => ‖u n‖)) (hv : Summable (fun n => ‖v n‖)) (r : ℤ) :
    Summable (fun n => inner ℂ (u n) (v (n+r))) := by
  have hp : Summable (fun p : ℤ × ℤ => ‖u p.1‖*‖v p.2‖) :=
    hu.mul_of_nonneg hv (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have hd := hp.comp_injective (show Function.Injective (fun n : ℤ => (n,n+r)) from
    fun _ _ h => congrArg Prod.fst h)
  apply hd.of_norm_bounded
  intro n
  exact norm_inner_le_norm _ _

 

theorem inner_tsum_diagonal {u v : ℤ → H} (hu : Summable u) (hv : Summable v)
    (r : ℤ) (hz : ∀ m n, n ≠ m+r → inner ℂ (u m) (v n) = 0) :
    inner ℂ (∑' m, u m) (∑' n, v n) = ∑' m, inner ℂ (u m) (v (m+r)) := by
  calc
    _ = ∑' m, inner ℂ (u m) (∑' n, v n) :=
      ((innerSL ℂ).flip (∑' n, v n)).map_tsum hu
    _ = _ := by
      apply tsum_congr
      intro m
      calc
        _ = ∑' n, inner ℂ (u m) (v n) := (innerSL ℂ (u m)).map_tsum hv
        _ = _ := tsum_eq_single (m+r) (fun n hn => hz m n hn)

end StronglyRationalVOA

namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
open UniformSpace
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

 

theorem hasSum_smeared_inner_homogeneous {a b x y : V} {d e D E : ℕ}
    (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    (hx : x ∈ A.grade D) (hy : y ∈ A.grade E)
    (hqa : A.IsQuasiPrimary a) (hha : U.IsHermitian d a)
    (hea : A.PolynomialEnergyBound a) (heb : A.PolynomialEnergyBound b)
    {f g : ℤ → ℂ} (hf : RapidCoefficients f) (hg : RapidCoefficients g)
    (hreal : ∀ n, star (f n) = f (-n)) :
    HasSum (fun m : ℤ => f m*g ((E : ℤ)-D-m)*
      inner ℂ x (A.physicalMode a d m (A.physicalMode b e ((E : ℤ)-D-m) y)))
      (inner ℂ (A.smearedMap a d hea f hf x) (A.smearedMap b e heb g hg y)) := by
  let u (m : ℤ) : Completion V := f m • (A.physicalMode a d m x : Completion V)
  let v (n : ℤ) : Completion V := g n • (A.physicalMode b e n y : Completion V)
  have hu : Summable (fun m => ‖u m‖) := A.summable_norm_physicalSmear hea d hf x
  have hv : Summable (fun n => ‖v n‖) := A.summable_norm_physicalSmear heb e hg y
  have hz : ∀ m n, n ≠ m+((E : ℤ)-D) → inner ℂ (u m) (v n) = 0 := by
    intro m n hne
    dsimp only [u,v]
    simp only [inner_smul_left,inner_smul_right,Completion.inner_coe]
    rw [U.physicalMode_cross_orthogonal ha hb hx hy m n (by omega),mul_zero,mul_zero]
  have H := (summable_inner_diagonal hu hv ((E : ℤ)-D)).hasSum
  rw [← inner_tsum_diagonal hu.of_norm hv.of_norm ((E : ℤ)-D) hz] at H
  have H' := (Equiv.neg ℤ).hasSum_iff.mpr H
  convert H' using 1
  ext m
  dsimp only [Function.comp_def,Equiv.neg_apply,u,v]
  simp only [Equiv.neg_apply,inner_smul_left,inner_smul_right,Completion.inner_coe,
    starRingEnd_apply,hreal,neg_neg,U.physicalMode_adjoint ha hqa hha]
  rw [show -m+((E : ℤ)-D) = (E : ℤ)-D-m by omega]
  ring
  rfl

end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

namespace StronglyRationalVOA.CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  (A : CFTTypeVOA V)

 

theorem hasSum_smeared_commutator_zero {a b : V} {d e : ℕ}
    (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    {f g : SmoothCircleFunction} (hfg : Disjoint (tsupport f) (tsupport g))
    (r : ℤ) (x y : V) :
    HasSum (fun m : ℤ => f.coefficient m*g.coefficient (r-m)*
      inner ℂ x (A.physicalMode a d m (A.physicalMode b e (r-m) y)-
        A.physicalMode b e (r-m) (A.physicalMode a d m y))) 0 := by
  let c (j : ℕ) : ℂ := inner ℂ x
    (mode A.fields (mode A.fields a j b) (r+d+e-2-j) y)
  have Hj (j : ℕ) : HasSum (fun m : ℤ =>
      Ring.choose ((m : ℂ)+((d : ℂ)-1)) j * f.coefficient m*g.coefficient (r-m)*c j) 0 := by
    simpa only [zero_mul] using
      (SmoothCircleFunction.hasSum_choose_convolution_zero hfg ((d : ℂ)-1) j r).mul_right (c j)
  have H : HasSum (fun m : ℤ => ∑ j ∈ Finset.range (d+e),
      Ring.choose ((m : ℂ)+((d : ℂ)-1)) j * f.coefficient m*g.coefficient (r-m)*c j) 0 := by
    simpa only [Finset.sum_const_zero] using
      (hasSum_sum (s := Finset.range (d+e)) (fun j _ => Hj j))
  have he (m : ℤ) : f.coefficient m*g.coefficient (r-m)*
      inner ℂ x (A.physicalMode a d m (A.physicalMode b e (r-m) y)-
        A.physicalMode b e (r-m) (A.physicalMode a d m y)) =
      ∑ j ∈ Finset.range (d+e),
      Ring.choose ((m : ℂ)+((d : ℂ)-1)) j * f.coefficient m*g.coefficient (r-m)*c j := by
    rw [A.physicalMode_commutator_finite ha hb,inner_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [inner_smul_right,c]
    rw [show m+(r-m)+(d : ℤ)+e-2-j = r+d+e-2-j by omega]
    rw [show (m : ℂ)+d-1 = (m : ℂ)+((d : ℂ)-1) by ring]
    ring
  simpa only [he] using H

namespace UnitaryStructure
variable {A} (U : A.UnitaryStructure)

 

theorem smearedMap_weak_commutation {a b : V} {d e : ℕ}
    (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    (hqa : A.IsQuasiPrimary a) (hqb : A.IsQuasiPrimary b)
    (hha : U.IsHermitian d a) (hhb : U.IsHermitian e b)
    (hea : A.PolynomialEnergyBound a) (heb : A.PolynomialEnergyBound b)
    {f g : SmoothCircleFunction} (hf : f.IsReal) (hg : g.IsReal)
    (hfg : Disjoint (tsupport f) (tsupport g)) (x y : V) :
    inner ℂ (A.smearedMap a d hea f.coefficient f.rapid_coefficients x)
      (A.smearedMap b e heb g.coefficient g.rapid_coefficients y) =
    inner ℂ (A.smearedMap b e heb g.coefficient g.rapid_coefficients x)
      (A.smearedMap a d hea f.coefficient f.rapid_coefficients y) := by
  have Hhom (D E : ℕ) (x y : V) (hx : x ∈ A.grade D) (hy : y ∈ A.grade E) :
      inner ℂ (A.smearedMap a d hea f.coefficient f.rapid_coefficients x)
        (A.smearedMap b e heb g.coefficient g.rapid_coefficients y) =
      inner ℂ (A.smearedMap b e heb g.coefficient g.rapid_coefficients x)
        (A.smearedMap a d hea f.coefficient f.rapid_coefficients y) := by
    let r : ℤ := (E : ℤ)-D
    have H1 := U.hasSum_smeared_inner_homogeneous ha hb hx hy hqa hha hea heb
      f.rapid_coefficients g.rapid_coefficients (SmoothCircleFunction.coefficient_real hf)
    have H2 := U.hasSum_smeared_inner_homogeneous hb ha hx hy hqb hhb heb hea
      g.rapid_coefficients f.rapid_coefficients (SmoothCircleFunction.coefficient_real hg)
    let R : ℤ ≃ ℤ :=
      { toFun := fun m => r-m
        invFun := fun m => r-m
        left_inv := fun m => by dsimp; omega
        right_inv := fun m => by dsimp; omega }
    have H2' := R.hasSum_iff.mpr H2
    have Hdiff := H1.sub H2'
    have Hz := A.hasSum_smeared_commutator_zero ha hb hfg r x y
    apply sub_eq_zero.mp
    apply Hdiff.unique
    convert Hz using 1
    ext m
    simp only [Function.comp_def,R,Equiv.coe_fn_mk]
    rw [show (E : ℤ)-D-(r-m) = m by dsimp [r]; omega]
    simp only [inner_sub_right]
    ring
  apply A.homogeneous_induction (P := fun x =>
      inner ℂ (A.smearedMap a d hea f.coefficient f.rapid_coefficients x)
        (A.smearedMap b e heb g.coefficient g.rapid_coefficients y) =
      inner ℂ (A.smearedMap b e heb g.coefficient g.rapid_coefficients x)
        (A.smearedMap a d hea f.coefficient f.rapid_coefficients y))
  · simp only [map_zero,inner_zero_left]
  · intro D x hx
    apply A.homogeneous_induction (P := fun y =>
        inner ℂ (A.smearedMap a d hea f.coefficient f.rapid_coefficients x)
          (A.smearedMap b e heb g.coefficient g.rapid_coefficients y) =
        inner ℂ (A.smearedMap b e heb g.coefficient g.rapid_coefficients x)
          (A.smearedMap a d hea f.coefficient f.rapid_coefficients y))
    · simp only [map_zero,inner_zero_right]
    · intro E y hy
      exact Hhom D E x y hx hy
    · intro y z hy hz
      simp only [map_add,inner_add_right,hy,hz]
  · intro x z hx hz
    simp only [map_add,inner_add_left,hx,hz]

end UnitaryStructure
end StronglyRationalVOA.CFTTypeVOA

namespace StronglyRationalVOA.ClosedGraphData
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace H] [CompleteSpace K]

def doubleUnitary (E : H ≃ₗᵢ[ℂ] K) : Double H ≃ₗᵢ[ℂ] Double K :=
  E.withLpProdCongr 2 E

omit [CompleteSpace H] [CompleteSpace K] in
@[simp] theorem doubleUnitary_apply (E : H ≃ₗᵢ[ℂ] K) (x : Double H) :
    doubleUnitary E x = WithLp.toLp 2 (E x.ofLp.1,E x.ofLp.2) := rfl

omit [CompleteSpace H] [CompleteSpace K] in
@[simp] theorem doubleUnitary_symm_apply (E : H ≃ₗᵢ[ℂ] K) (x : Double K) :
    (doubleUnitary E).symm x = WithLp.toLp 2 (E.symm x.ofLp.1,E.symm x.ofLp.2) := rfl

omit [CompleteSpace H] [CompleteSpace K] in
theorem mem_graph_transport (E : H ≃ₗᵢ[ℂ] K) (T : K →ₗ.[ℂ] K) (x : Double H) :
    x ∈ graph (OperatorTransport.transport E T) ↔ doubleUnitary E x ∈ graph T :=
  OperatorTransport.mem_graph_iff E T x.ofLp.1 x.ofLp.2

 

theorem projection_transport (E : H ≃ₗᵢ[ℂ] K) (T : K →ₗ.[ℂ] K) (hT : T.IsClosed)
    (x : Double H) :
    projection (OperatorTransport.transport E T) (OperatorTransport.closed E hT) x =
      (doubleUnitary E).symm (projection T hT (doubleUnitary E x)) := by
  let : IsClosed (graph T : Set (Double K)) := graph_closed hT
  let : IsClosed (graph (OperatorTransport.transport E T) : Set (Double H)) :=
    graph_closed (OperatorTransport.closed E hT)
  change (graph (OperatorTransport.transport E T)).starProjection x = _
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · apply (mem_graph_transport E T _).mpr
    rw [(doubleUnitary E).apply_symm_apply]
    exact (graph T).starProjection_apply_mem _
  · intro y hy
    rw [← (doubleUnitary E).inner_map_map,map_sub,(doubleUnitary E).apply_symm_apply]
    exact (graph T).starProjection_inner_eq_zero _ _ ((mem_graph_transport E T y).mp hy)

omit [CompleteSpace H] [CompleteSpace K] in
theorem coordinate_doubleUnitary (E : H ≃ₗᵢ[ℂ] K) (i : Bool) (x : Double H) :
    coordinate i (doubleUnitary E x) = E (coordinate i x) := by
  cases i <;> rfl

omit [CompleteSpace H] [CompleteSpace K] in
theorem doubleUnitary_inclusion (E : H ≃ₗᵢ[ℂ] K) (i : Bool) (x : H) :
    doubleUnitary E (inclusion i x) = inclusion i (E x) := by
  cases i <;> simp [doubleUnitary_apply,inclusion]

 
theorem entry_transport (E : H ≃ₗᵢ[ℂ] K) (T : K →ₗ.[ℂ] K) (hT : T.IsClosed)
    (i j : Bool) (x : H) :
    entry (OperatorTransport.transport E T) (OperatorTransport.closed E hT) i j x =
      E.symm (entry T hT i j (E x)) := by
  change coordinate i (projection (OperatorTransport.transport E T)
      (OperatorTransport.closed E hT) (inclusion j x)) = _
  rw [projection_transport,doubleUnitary_inclusion]
  change coordinate i (doubleUnitary E.symm (projection T hT (inclusion j (E x)))) = _
  rw [coordinate_doubleUnitary]
  rfl

theorem commute_transport (E : H ≃ₗᵢ[ℂ] K) (A B : K →ₗ.[ℂ] K)
    (hA : A.IsClosed) (hB : B.IsClosed) (i j k l : Bool)
    (hc : Commute (entry A hA i j) (entry B hB k l)) :
    Commute (entry (OperatorTransport.transport E A) (OperatorTransport.closed E hA) i j)
      (entry (OperatorTransport.transport E B) (OperatorTransport.closed E hB) k l) := by
  apply ContinuousLinearMap.ext
  intro x
  change entry (OperatorTransport.transport E A) (OperatorTransport.closed E hA) i j
    (entry (OperatorTransport.transport E B) (OperatorTransport.closed E hB) k l x) =
    entry (OperatorTransport.transport E B) (OperatorTransport.closed E hB) k l
    (entry (OperatorTransport.transport E A) (OperatorTransport.closed E hA) i j x)
  simp only [entry_transport E A hA,entry_transport E B hB,E.apply_symm_apply]
  have hx := congrArg (fun T : K →L[ℂ] K => T (E x)) hc.eq
  change entry A hA i j (entry B hB k l (E x)) =
    entry B hB k l (entry A hA i j (E x)) at hx
  exact congrArg (fun y : K => E.symm y) hx

end StronglyRationalVOA.ClosedGraphData

namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
open UniformSpace
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

include U in
 

theorem firstOrder_strongCommutation (M N K L : V →ₗ[ℂ] Completion V) {C D E F : ℝ}
    (hM : ∀ a, ‖M a‖ ≤ C*‖A.energyShift a‖)
    (hN : ∀ a, ‖N a‖ ≤ D*‖A.energyShift a‖)
    (hK : ∀ a, ‖K a‖ ≤ E*‖A.energyShift a‖)
    (hL : ∀ a, ‖L a‖ ≤ F*‖A.energyShift a‖)
    (hsM : ∀ x y : V, inner ℂ (M x) (y : Completion V) = inner ℂ (x : Completion V) (M y))
    (hsN : ∀ x y : V, inner ℂ (N x) (y : Completion V) = inner ℂ (x : Completion V) (N y))
    (hkM : ∀ x y : V, inner ℂ (M x) (A.energyShift y : Completion V)-
      inner ℂ (A.energyShift x : Completion V) (M y) = inner ℂ (K x) (y : Completion V))
    (hkN : ∀ x y : V, inner ℂ (N x) (A.energyShift y : Completion V)-
      inner ℂ (A.energyShift x : Completion V) (N y) = inner ℂ (L x) (y : Completion V))
    (hw : ∀ x y, inner ℂ (M x) (N y) = inner ℂ (N x) (M y)) (i j k l : Bool) :
    Commute (ClosedGraphData.entry (HilbertCore.operator M).closure
      (HilbertCore.closable hsM).closure_isClosed i j)
      (ClosedGraphData.entry (HilbertCore.operator N).closure
        (HilbertCore.closable hsN).closure_isClosed k l) := by
  let : ∀ d, FiniteDimensional ℂ (A.grade d) := A.grade_finite
  have transBound (T : V →ₗ[ℂ] Completion V) {q : ℝ}
      (ht : ∀ a, ‖T a‖ ≤ q*‖A.energyShift a‖) :
      ∀ x, ‖U.spectralCoreMap T x‖ ≤
        q*‖HilbertScale.coreDiagonal (fun d : ℕ => ((1+(d : ℝ) : ℝ) : ℂ)) x‖ := by
    intro x
    obtain ⟨v,rfl⟩ := U.coreEnergyCoordinates.surjective x
    simpa only [U.spectralCoreMap_apply,U.coreEnergyCoordinates_energyShift,
      U.energyCoordinates.norm_map,Completion.norm_coe] using ht v
  have transSym (T : V →ₗ[ℂ] Completion V)
      (hs : ∀ x y : V, inner ℂ (T x) (y : Completion V) = inner ℂ (x : Completion V) (T y)) :
      ∀ x y : HilbertScale.finiteCore (G := fun d => A.grade d),
        inner ℂ (U.spectralCoreMap T x) y =
          inner ℂ (x : HilbertScale.Space _) (U.spectralCoreMap T y) := by
    intro x y
    obtain ⟨v,rfl⟩ := U.coreEnergyCoordinates.surjective x
    obtain ⟨w,rfl⟩ := U.coreEnergyCoordinates.surjective y
    simpa only [U.spectralCoreMap_apply,U.coreEnergyCoordinates_coe,
      U.energyCoordinates.inner_map_map] using hs v w
  have transComm (T R : V →ₗ[ℂ] Completion V)
      (hk : ∀ x y : V, inner ℂ (T x) (A.energyShift y : Completion V)-
        inner ℂ (A.energyShift x : Completion V) (T y) = inner ℂ (R x) (y : Completion V)) :
      ∀ x y : HilbertScale.finiteCore (G := fun d => A.grade d),
        inner ℂ (U.spectralCoreMap T x)
            (HilbertScale.coreDiagonal (fun d : ℕ => ((1+(d : ℝ) : ℝ) : ℂ)) y)-
          inner ℂ (HilbertScale.coreDiagonal (fun d : ℕ => ((1+(d : ℝ) : ℝ) : ℂ)) x)
            (U.spectralCoreMap T y) = inner ℂ (U.spectralCoreMap R x) y := by
    intro x y
    obtain ⟨v,rfl⟩ := U.coreEnergyCoordinates.surjective x
    obtain ⟨w,rfl⟩ := U.coreEnergyCoordinates.surjective y
    simpa only [U.spectralCoreMap_apply,U.coreEnergyCoordinates_coe,
      U.coreEnergyCoordinates_energyShift,U.energyCoordinates.inner_map_map] using hk v w
  have hw' : ∀ x y, inner ℂ (U.spectralCoreMap M x) (U.spectralCoreMap N y) =
      inner ℂ (U.spectralCoreMap N x) (U.spectralCoreMap M y) := by
    intro x y
    obtain ⟨v,rfl⟩ := U.coreEnergyCoordinates.surjective x
    obtain ⟨w,rfl⟩ := U.coreEnergyCoordinates.surjective y
    simpa only [U.spectralCoreMap_apply,U.energyCoordinates.inner_map_map] using hw v w
  have hclM := HilbertScale.coreOperator_closable (U.spectralCoreMap M) (transSym M hsM)
  have hclN := HilbertScale.coreOperator_closable (U.spectralCoreMap N) (transSym N hsN)
  have H := HilbertScale.coreOperator_strongCommutation (fun d : ℕ => 1+(d : ℝ))
    (fun d => by have := Nat.cast_nonneg (α := ℝ) d; linarith)
    (U.spectralCoreMap M) (U.spectralCoreMap N) (U.spectralCoreMap K) (U.spectralCoreMap L)
    (transBound M hM) (transBound N hN) (transBound K hK) (transBound L hL)
    (transSym M hsM) (transSym N hsN) (transComm M K hkM) (transComm N L hkN) hw' i j k l
  have HM : OperatorTransport.transport U.energyCoordinates
      (HilbertScale.coreOperator (U.spectralCoreMap M)).closure = (HilbertCore.operator M).closure := by
    rw [← OperatorTransport.closure U.energyCoordinates hclM,U.spectralCoreOperator_transport]
  have HN : OperatorTransport.transport U.energyCoordinates
      (HilbertScale.coreOperator (U.spectralCoreMap N)).closure = (HilbertCore.operator N).closure := by
    rw [← OperatorTransport.closure U.energyCoordinates hclN,U.spectralCoreOperator_transport]
  have HT := ClosedGraphData.commute_transport U.energyCoordinates
    (HilbertScale.coreOperator (U.spectralCoreMap M)).closure
    (HilbertScale.coreOperator (U.spectralCoreMap N)).closure
    hclM.closure_isClosed hclN.closure_isClosed i j k l H
  simpa only [HM,HN] using HT

 

theorem closedSmoothField_strongCommutation_of_firstOrder (hc : A.toVertexAlgebra.C2Cofinite)
    {a b : V} {d e p q : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    (hqa : A.IsQuasiPrimary a) (hqb : A.IsQuasiPrimary b)
    (hha : U.IsHermitian d a) (hhb : U.IsHermitian e b) {C D : ℝ}
    (hea : ∀ n v, ‖A.physicalMode a d n v‖ ≤ C*(1+|(n : ℝ)|)^p*‖A.energyShift v‖)
    (heb : ∀ n v, ‖A.physicalMode b e n v‖ ≤ D*(1+|(n : ℝ)|)^q*‖A.energyShift v‖)
    {f g : SmoothCircleFunction} (hf : f.IsReal) (hg : g.IsReal)
    (hfg : Disjoint (tsupport f) (tsupport g)) (i j k l : Bool) :
    Commute (ClosedGraphData.entry (U.closedSmoothField hc a d f)
        (U.closedSmoothField_isClosed hc ha f) i j)
      (ClosedGraphData.entry (U.closedSmoothField hc b e g)
        (U.closedSmoothField_isClosed hc hb g) k l) := by
  have hfr := f.rapid_coefficients
  have hgr := g.rapid_coefficients
  have hfr' : RapidCoefficients (fun n => -(n : ℂ)*f.coefficient n) := by
    simpa only [neg_mul,one_mul] using hfr.int_mul.smul (-1)
  have hgr' : RapidCoefficients (fun n => -(n : ℂ)*g.coefficient n) := by
    simpa only [neg_mul,one_mul] using hgr.int_mul.smul (-1)
  apply U.firstOrder_strongCommutation
    (A.smearedMap a d (U.polynomialEnergyBounds hc a) f.coefficient hfr)
    (A.smearedMap b e (U.polynomialEnergyBounds hc b) g.coefficient hgr)
    (A.smearedMap a d (U.polynomialEnergyBounds hc a) (fun n => -(n : ℂ)*f.coefficient n) hfr')
    (A.smearedMap b e (U.polynomialEnergyBounds hc b) (fun n => -(n : ℂ)*g.coefficient n) hgr')
  · intro v
    simpa only [pow_one] using A.smearedMap_bound (k := 1) (U.polynomialEnergyBounds hc a) hfr
      (by simpa only [pow_one] using hea) v
  · intro v
    simpa only [pow_one] using A.smearedMap_bound (k := 1) (U.polynomialEnergyBounds hc b) hgr
      (by simpa only [pow_one] using heb) v
  · intro v
    simpa only [pow_one] using A.smearedMap_bound (k := 1) (U.polynomialEnergyBounds hc a) hfr'
      (by simpa only [pow_one] using hea) v
  · intro v
    simpa only [pow_one] using A.smearedMap_bound (k := 1) (U.polynomialEnergyBounds hc b) hgr'
      (by simpa only [pow_one] using heb) v
  · exact U.smearedMap_symmetric ha hqa hha (U.polynomialEnergyBounds hc a) hfr
      (SmoothCircleFunction.coefficient_real hf)
  · exact U.smearedMap_symmetric hb hqb hhb (U.polynomialEnergyBounds hc b) hgr
      (SmoothCircleFunction.coefficient_real hg)
  · exact U.smearedMap_energy_commutator ha hqa hha (U.polynomialEnergyBounds hc a) hfr
      (SmoothCircleFunction.coefficient_real hf)
  · exact U.smearedMap_energy_commutator hb hqb hhb (U.polynomialEnergyBounds hc b) hgr
      (SmoothCircleFunction.coefficient_real hg)
  · exact U.smearedMap_weak_commutation ha hb hqa hqb hha hhb
      (U.polynomialEnergyBounds hc a) (U.polynomialEnergyBounds hc b) hf hg hfg

end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open scoped Topology
namespace StronglyRationalVOA.BoundedFlow
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance coefficientDifferentiatedNormedAlgebra : NormedAlgebra ℚ (H →L[ℂ] H) :=
  .restrictScalars ℚ ℂ _
end StronglyRationalVOA.BoundedFlow

end

end OAI
