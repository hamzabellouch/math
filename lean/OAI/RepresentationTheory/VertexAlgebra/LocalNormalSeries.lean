import Mathlib
import OAI.RepresentationTheory.VertexAlgebra.SmoothSmearShift

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
open scoped ContDiff
open MeasureTheory
open MeasureTheory Set
open MeasureTheory Set Filter
open scoped Topology Interval
open Set Filter
open UniformSpace Set
open UniformSpace Filter
open UniformSpace Filter Set
open UniformSpace Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter MeasureTheory Set
open Filter Set
open Filter UniformSpace
open Set MeasureTheory
open Set
open MeasureTheory Filter
open Set MeasureTheory Filter UniformSpace
open Set UniformSpace
open Set UniformSpace Filter
open Set MeasureTheory Filter
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma local_normal_series_matrix (hc : A.toVertexAlgebra.C2Cofinite)
    {a b x y : V} {d e D E : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    (hx : x ∈ A.grade D) (hy : y ∈ A.grade E)
    {χ f : SmoothCircleFunction}
    (hχ : Disjoint (tsupport (χ.add (SmoothCircleFunction.constant (-1)))) (tsupport f)) :
    (∑' j : ℕ, inner ℂ (x:Completion V)
      (U.smoothSmear hc ha (χ.rapid_coefficients.shift (-(j+1:ℤ)))
        (U.smoothSmear hc hb (f.rapid_coefficients.shift (j+1:ℤ)) (U.smoothCoreVector y)) : Completion V))+
    (∑' j : ℕ, inner ℂ (x:Completion V)
      (U.smoothSmear hc hb (f.rapid_coefficients.shift (-(j:ℤ)))
        (U.smoothSmear hc ha (χ.rapid_coefficients.shift (j:ℤ)) (U.smoothCoreVector y)) : Completion V)) =
    f.coefficient ((E:ℤ)-D)*inner ℂ x (A.normalAt a b d e ((E:ℤ)-D) 0 y) := by
  let L (i : ℤ) (j : ℕ) : ℂ := χ.coefficient i*f.coefficient ((E:ℤ)-D-i)*
    inner ℂ x (A.physicalMode a d (i-1-j) (A.physicalMode b e ((E:ℤ)-D-i+1+j) y))
  let R (i : ℤ) (j : ℕ) : ℂ := χ.coefficient i*f.coefficient ((E:ℤ)-D-i)*
    inner ℂ x (A.physicalMode b e ((E:ℤ)-D-i-j) (A.physicalMode a d (i+j) y))
  have hL : Summable (Function.uncurry L) := by
    have H := (innerSL ℂ (x:Completion V)).summable
      (U.summable_norm_normal_left hc ha hb hy D χ.rapid_coefficients f.rapid_coefficients).of_norm
    simp only [innerSL_apply_apply,inner_smul_right,Completion.inner_coe] at H
    convert! H using 1
  have hR : Summable (Function.uncurry R) := by
    have H := (innerSL ℂ (x:Completion V)).summable
      (U.summable_norm_normal_right hc ha hb hy D χ.rapid_coefficients f.rapid_coefficients).of_norm
    simp only [innerSL_apply_apply,inner_smul_right,Completion.inner_coe] at H
    convert! H using 1
  have hLR (i : ℤ) : (∑' j, L i j)+(∑' j, R i j)=
      χ.coefficient i*f.coefficient ((E:ℤ)-D-i)*inner ℂ x (A.normalAt a b d e ((E:ℤ)-D) i y) := by
    have H := ((innerSL ℂ (x:Completion V)).hasSum
      (A.hasSum_normalAt_completion a b d e ((E:ℤ)-D) i y)).mul_left
        (χ.coefficient i*f.coefficient ((E:ℤ)-D-i))
    have he : HasSum (fun j => L i j+R i j)
        (χ.coefficient i*f.coefficient ((E:ℤ)-D-i)*inner ℂ x (A.normalAt a b d e ((E:ℤ)-D) i y)) := by
      simpa only [L,R,innerSL_apply_apply,inner_add_right,Completion.inner_coe,mul_add] using H
    exact (Summable.tsum_add (hL.prod_factor i) (hR.prod_factor i)).symm.trans he.tsum_eq
  have hcut := (innerSL ℂ (x:Completion V)).hasSum (A.hasSum_normalAt_cutoff ha hb hχ ((E:ℤ)-D) y)
  have hcut' : HasSum (fun i : ℤ => χ.coefficient i*f.coefficient ((E:ℤ)-D-i)*
      inner ℂ x (A.normalAt a b d e ((E:ℤ)-D) i y))
      (f.coefficient ((E:ℤ)-D)*inner ℂ x (A.normalAt a b d e ((E:ℤ)-D) 0 y)) := by
    simpa only [innerSL_apply_apply,inner_smul_right,Completion.inner_coe] using hcut
  calc
    _ = (∑' j, ∑' i, L i j)+(∑' j, ∑' i, R i j) := by
      congr 1
      · apply tsum_congr; intro j
        exact (U.hasSum_modulated_left_matrix hc ha hb hx hy χ.rapid_coefficients f.rapid_coefficients j).tsum_eq.symm
      · apply tsum_congr; intro j
        exact (U.hasSum_modulated_right_matrix hc ha hb hx hy χ.rapid_coefficients f.rapid_coefficients j).tsum_eq.symm
    _ = (∑' i, ∑' j, L i j)+(∑' i, ∑' j, R i j) := by rw [hL.tsum_comm,hR.tsum_comm]
    _ = ∑' i, ((∑' j, L i j)+(∑' j, R i j)) := (Summable.tsum_add hL.prod hR.prod).symm
    _ = _ := by simp_rw [hLR]; exact hcut'.tsum_eq
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma modulated_product_uniform_bound (hc : A.toVertexAlgebra.C2Cofinite)
    {a b : V} {d e : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    {f g : ℤ → ℂ} (hf : RapidCoefficients f) (hg : RapidCoefficients g)
    : ∃ m : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ (j : ℕ) (x : U.smoothEnergySpace),
      ‖((U.smoothSmear hc ha (hg.shift (-(j:ℤ))))
        (U.smoothSmear hc hb (hf.shift (j:ℤ)) x) : Completion V)‖ ≤
        K/(1+(j:ℝ))^2*‖U.smoothEnergyPower m x‖ := by
  obtain ⟨C,hC,p,k,hA⟩ := (U.polynomialEnergyBounds hc a).physical A d
  obtain ⟨D,hD,q,l,hB⟩ := (U.polynomialEnergyBounds hc b).physical A e
  let R := p+q+k+2
  let K := (coefficientSeminorm g p*C)*(coefficientSeminorm f (q+R+k)*D)
  have hFg := coefficientSeminorm_nonneg g p
  have hFf := coefficientSeminorm_nonneg f (q+R+k)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨l+R+k,K,hK,?_⟩
  intro j x
  have ho := U.smoothSmear_shift_bound hc ha hC.le hA hg (-(j:ℤ))
    (U.smoothSmear hc hb (hf.shift (j:ℤ)) x)
  simp only [Int.cast_neg,Int.cast_natCast,abs_neg,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) j)] at ho
  have hi := U.smoothSmear_positive_shift_sobolev_bound hc hb hD.le hB hf R j k x
  change _ ≤ (coefficientSeminorm f (q+R+k)*D*(1+(j:ℝ))^(q+k)/(1+(j:ℝ))^R)*
    ‖U.smoothEnergyPower (l+R+k) x‖ at hi
  apply ho.trans
  calc
    _ ≤ (coefficientSeminorm g p*C*(1+(j:ℝ))^p)*
      ((coefficientSeminorm f (q+R+k)*D*(1+(j:ℝ))^(q+k)/(1+(j:ℝ))^R)*
      ‖U.smoothEnergyPower (l+R+k) x‖) := by gcongr
    _ = _ := by
      dsimp [K,R]
      rw [show p+q+k+2=p+(q+k)+2 by omega]
      simp only [pow_add]
      field_simp
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
include U in
lemma summable_norm_normal_left_shift (hc : A.toVertexAlgebra.C2Cofinite)
    {a b y : V} {d e E : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    (hy : y ∈ A.grade E) (D : ℕ) (c : ℤ)
    {f g : ℤ → ℂ} (hf : RapidCoefficients f) (hg : RapidCoefficients g) :
    Summable (fun q : ℤ × ℕ => ‖(f q.1*g ((E:ℤ)-D-q.1)) •
      (A.physicalMode a d (q.1+c-1-q.2)
        (A.physicalMode b e ((E:ℤ)-D-(q.1+c)+1+q.2) y) : Completion V)‖) := by
  have H := U.summable_norm_normal_left hc ha hb hy D (hf.shift c) (hg.shift (-c))
  let σ : ℤ × ℕ ≃ ℤ × ℕ := Equiv.prodCongr (Equiv.addRight c) (Equiv.refl ℕ)
  have H' := H.comp_injective σ.injective
  convert! H' using 1
  funext q
  simp only [Function.comp_apply,σ,Equiv.prodCongr_apply,Prod.map,Equiv.coe_addRight,Equiv.refl_apply]
  have h1 : q.1+c-c=q.1 := by omega
  have h2 : (E:ℤ)-D-(q.1+c)-(-c)=(E:ℤ)-D-q.1 := by omega
  rw [h1,h2]
include U in
lemma summable_norm_normal_right_shift (hc : A.toVertexAlgebra.C2Cofinite)
    {a b y : V} {d e E : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    (hy : y ∈ A.grade E) (D : ℕ) (c : ℤ)
    {f g : ℤ → ℂ} (hf : RapidCoefficients f) (hg : RapidCoefficients g) :
    Summable (fun q : ℤ × ℕ => ‖(f q.1*g ((E:ℤ)-D-q.1)) •
      (A.physicalMode b e ((E:ℤ)-D-(q.1+c)-q.2)
        (A.physicalMode a d (q.1+c+q.2) y) : Completion V)‖) := by
  have H := U.summable_norm_normal_right hc ha hb hy D (hf.shift c) (hg.shift (-c))
  let σ : ℤ × ℕ ≃ ℤ × ℕ := Equiv.prodCongr (Equiv.addRight c) (Equiv.refl ℕ)
  have H' := H.comp_injective σ.injective
  convert! H' using 1
  funext q
  simp only [Function.comp_apply,σ,Equiv.prodCongr_apply,Prod.map,Equiv.coe_addRight,Equiv.refl_apply]
  have h1 : q.1+c-c=q.1 := by omega
  have h2 : (E:ℤ)-D-(q.1+c)-(-c)=(E:ℤ)-D-q.1 := by omega
  rw [h1,h2]
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace
namespace StronglyRationalVOA.CFTTypeVOA
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (A : CFTTypeVOA V)
 

lemma hasSum_normalAt_cutoff_shift {a b : V} {d e : ℕ}
    (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    {χ f : SmoothCircleFunction}
    (hχ : Disjoint (tsupport (χ.add (SmoothCircleFunction.constant (-1)))) (tsupport f))
    (k c : ℤ) (v : V) :
    HasSum (fun i : ℤ => (χ.coefficient i*f.coefficient (k-i)) •
      (A.normalAt a b d e k (i+c) v : Completion V))
      (f.coefficient k • (A.normalAt a b d e k c v : Completion V)) := by
  classical
  have hs (s : Finset ℕ) (g : ℕ → V) :
      ((∑ j ∈ s, g j : V) : Completion V)=∑ j ∈ s, (g j : Completion V) :=
    map_sum (Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V) g s
  let z : Completion V := A.physicalMode (mode A.fields a (-1) b) (d+e) k v
  let w (j : ℕ) : Completion V := mode A.fields (mode A.fields a j b) (k+d+e-2-j) v
  have H0 : HasSum (fun i : ℤ => (χ.coefficient i*f.coefficient (k-i)) • z)
      (f.coefficient k • z) := by
    have h := (SmoothCircleFunction.hasSum_choose_cutoff hχ 0 0 k).smul_const z
    simpa using h
  have Hj (j : ℕ) := (SmoothCircleFunction.hasSum_choose_cutoff hχ ((c:ℂ)+(d:ℂ)-1) (j+1) k).smul_const (w j)
  have H := H0.add (hasSum_sum (s := Finset.range (d+e)) (fun j _ => Hj j))
  have he (i : ℤ) : (χ.coefficient i*f.coefficient (k-i)) •
      (A.normalAt a b d e k (i+c) v : Completion V)=
      (χ.coefficient i*f.coefficient (k-i)) • z+
        ∑ j ∈ Finset.range (d+e),
          (Ring.choose ((i:ℂ)+((c:ℂ)+(d:ℂ)-1)) (j+1)*χ.coefficient i*f.coefficient (k-i)) • w j := by
    rw [A.normalAt_choose ha hb]
    simp only [Int.cast_add,Completion.coe_add,hs,Completion.coe_smul,smul_add,Finset.smul_sum,smul_smul]
    apply congrArg₂ (· + ·) rfl
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [w]
    congr 1
    rw [show (i:ℂ)+c+d-1=(i:ℂ)+((c:ℂ)+(d:ℂ)-1) by ring]
    ring
  have hz : f.coefficient k • (A.normalAt a b d e k c v : Completion V)=
      f.coefficient k • z+∑ j ∈ Finset.range (d+e),
        (Ring.choose ((c:ℂ)+(d:ℂ)-1) (j+1)*f.coefficient k) • w j := by
    rw [A.normalAt_choose ha hb]
    simp only [Completion.coe_add,hs,Completion.coe_smul,
      smul_add,Finset.smul_sum,smul_smul]
    apply congrArg₂ (· + ·) rfl
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [w]
    rw [mul_comm]
  rw [hz]
  convert H using 1
  exact funext he
lemma hasSum_vertex_normal_cutoff {a b : V} {d e : ℕ}
    (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    {χ f : SmoothCircleFunction}
    (hχ : Disjoint (tsupport (χ.add (SmoothCircleFunction.constant (-1)))) (tsupport f))
    (k : ℤ) (v : V) :
    HasSum (fun i : ℤ => (χ.coefficient i*f.coefficient (k-i)) •
      (A.normalAt a b d e k (i+(1-(d:ℤ))) v : Completion V))
      (f.coefficient k • (A.physicalMode (mode A.fields a (-1) b) (d+e) k v : Completion V)) := by
  simpa only [A.normalAt_vertex_product] using A.hasSum_normalAt_cutoff_shift ha hb hχ k (1-(d:ℤ)) v
end StronglyRationalVOA.CFTTypeVOA

open UniformSpace
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma hasSum_modulated_left_matrix_shift (hc : A.toVertexAlgebra.C2Cofinite)
    {a b x y : V} {d e D E : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    (hx : x ∈ A.grade D) (hy : y ∈ A.grade E)
    {f g : ℤ → ℂ} (hf : RapidCoefficients f) (hg : RapidCoefficients g) (j : ℕ) (c : ℤ) :
    HasSum (fun i : ℤ => f i*g ((E:ℤ)-D-i)*
      inner ℂ x (A.physicalMode a d (i+c-1-j) (A.physicalMode b e ((E:ℤ)-D-(i+c)+1+j) y)))
      (inner ℂ (x:Completion V) (U.smoothSmear hc ha (hf.shift (c-(j+1:ℤ)))
        (U.smoothSmear hc hb (hg.shift ((j+1:ℤ)-c)) (U.smoothCoreVector y)) : Completion V)) := by
  have H := U.hasSum_smoothSmear_product_matrix hc ha hb hx hy
    (hf.shift (c-(j+1:ℤ))) (hg.shift ((j+1:ℤ)-c))
  have H' := (Equiv.subLeft ((E:ℤ)-D-c+j+1)).hasSum_iff.mpr H
  convert! H' using 1
  funext i
  simp only [Function.comp_apply,Equiv.subLeft_apply]
  have h1 : (E:ℤ)-D-((E:ℤ)-D-c+j+1-i)-(c-(j+1))=i := by omega
  have h2 : (E:ℤ)-D-c+j+1-i-((j+1)-c)=(E:ℤ)-D-i := by omega
  have h3 : (E:ℤ)-D-((E:ℤ)-D-c+j+1-i)=i+c-1-j := by omega
  have h4 : (E:ℤ)-D-c+j+1-i=(E:ℤ)-D-(i+c)+1+j := by omega
  rw [h1,h2,h3,h4]

lemma hasSum_modulated_right_matrix_shift (hc : A.toVertexAlgebra.C2Cofinite)
    {a b x y : V} {d e D E : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    (hx : x ∈ A.grade D) (hy : y ∈ A.grade E)
    {f g : ℤ → ℂ} (hf : RapidCoefficients f) (hg : RapidCoefficients g) (j : ℕ) (c : ℤ) :
    HasSum (fun i : ℤ => f i*g ((E:ℤ)-D-i)*
      inner ℂ x (A.physicalMode b e ((E:ℤ)-D-(i+c)-j) (A.physicalMode a d (i+c+j) y)))
      (inner ℂ (x:Completion V) (U.smoothSmear hc hb (hg.shift (-(j+c:ℤ)))
        (U.smoothSmear hc ha (hf.shift (j+c:ℤ)) (U.smoothCoreVector y)) : Completion V)) := by
  have H := U.hasSum_smoothSmear_product_matrix hc hb ha hx hy (hg.shift (-(j+c:ℤ))) (hf.shift (j+c:ℤ))
  have H' := (Equiv.addRight (j+c:ℤ)).hasSum_iff.mpr H
  convert! H' using 1
  funext i
  simp only [Function.comp_apply,Equiv.coe_addRight]
  have h1 : (E:ℤ)-D-(i+(j+c))-(-(j+c))=(E:ℤ)-D-i := by omega
  have h2 : i+(j+c)-(j+c)=i := by omega
  have h3 : (E:ℤ)-D-(i+(j+c))=(E:ℤ)-D-(i+c)-j := by omega
  have h4 : i+(j+c)=i+c+j := by omega
  rw [h1,h2,h3,h4,mul_comm (g _) (f _)]
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
 

lemma local_normal_series_matrix_shift (hc : A.toVertexAlgebra.C2Cofinite)
    {a b x y : V} {d e D E : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    (hx : x ∈ A.grade D) (hy : y ∈ A.grade E) (c : ℤ)
    {χ f : SmoothCircleFunction}
    (hχ : Disjoint (tsupport (χ.add (SmoothCircleFunction.constant (-1)))) (tsupport f)) :
    (∑' j : ℕ, inner ℂ (x:Completion V)
      (U.smoothSmear hc ha (χ.rapid_coefficients.shift (c-(j+1:ℤ)))
        (U.smoothSmear hc hb (f.rapid_coefficients.shift ((j+1:ℤ)-c)) (U.smoothCoreVector y)) : Completion V))+
    (∑' j : ℕ, inner ℂ (x:Completion V)
      (U.smoothSmear hc hb (f.rapid_coefficients.shift (-(j+c:ℤ)))
        (U.smoothSmear hc ha (χ.rapid_coefficients.shift (j+c:ℤ)) (U.smoothCoreVector y)) : Completion V)) =
    f.coefficient ((E:ℤ)-D)*inner ℂ x (A.normalAt a b d e ((E:ℤ)-D) c y) := by
  let L (i : ℤ) (j : ℕ) : ℂ := χ.coefficient i*f.coefficient ((E:ℤ)-D-i)*
    inner ℂ x (A.physicalMode a d (i+c-1-j) (A.physicalMode b e ((E:ℤ)-D-(i+c)+1+j) y))
  let R (i : ℤ) (j : ℕ) : ℂ := χ.coefficient i*f.coefficient ((E:ℤ)-D-i)*
    inner ℂ x (A.physicalMode b e ((E:ℤ)-D-(i+c)-j) (A.physicalMode a d (i+c+j) y))
  have hL : Summable (Function.uncurry L) := by
    have H := (innerSL ℂ (x:Completion V)).summable
      (U.summable_norm_normal_left_shift hc ha hb hy D c χ.rapid_coefficients f.rapid_coefficients).of_norm
    simp only [innerSL_apply_apply,inner_smul_right,Completion.inner_coe] at H
    convert! H using 1
  have hR : Summable (Function.uncurry R) := by
    have H := (innerSL ℂ (x:Completion V)).summable
      (U.summable_norm_normal_right_shift hc ha hb hy D c χ.rapid_coefficients f.rapid_coefficients).of_norm
    simp only [innerSL_apply_apply,inner_smul_right,Completion.inner_coe] at H
    convert! H using 1
  have hLR (i : ℤ) : (∑' j, L i j)+(∑' j, R i j)=
      χ.coefficient i*f.coefficient ((E:ℤ)-D-i)*inner ℂ x (A.normalAt a b d e ((E:ℤ)-D) (i+c) y) := by
    have H := ((innerSL ℂ (x:Completion V)).hasSum
      (A.hasSum_normalAt_completion a b d e ((E:ℤ)-D) (i+c) y)).mul_left
        (χ.coefficient i*f.coefficient ((E:ℤ)-D-i))
    have he : HasSum (fun j => L i j+R i j)
        (χ.coefficient i*f.coefficient ((E:ℤ)-D-i)*inner ℂ x (A.normalAt a b d e ((E:ℤ)-D) (i+c) y)) := by
      simpa only [L,R,innerSL_apply_apply,inner_add_right,Completion.inner_coe,mul_add] using H
    exact (Summable.tsum_add (hL.prod_factor i) (hR.prod_factor i)).symm.trans he.tsum_eq
  have hcut := (innerSL ℂ (x:Completion V)).hasSum (A.hasSum_normalAt_cutoff_shift ha hb hχ ((E:ℤ)-D) c y)
  have hcut' : HasSum (fun i : ℤ => χ.coefficient i*f.coefficient ((E:ℤ)-D-i)*
      inner ℂ x (A.normalAt a b d e ((E:ℤ)-D) (i+c) y))
      (f.coefficient ((E:ℤ)-D)*inner ℂ x (A.normalAt a b d e ((E:ℤ)-D) c y)) := by
    simpa only [innerSL_apply_apply,inner_smul_right,Completion.inner_coe] using hcut
  calc
    _ = (∑' j, ∑' i, L i j)+(∑' j, ∑' i, R i j) := by
      congr 1
      · apply tsum_congr; intro j
        exact (U.hasSum_modulated_left_matrix_shift hc ha hb hx hy χ.rapid_coefficients f.rapid_coefficients j c).tsum_eq.symm
      · apply tsum_congr; intro j
        exact (U.hasSum_modulated_right_matrix_shift hc ha hb hx hy χ.rapid_coefficients f.rapid_coefficients j c).tsum_eq.symm
    _ = (∑' i, ∑' j, L i j)+(∑' i, ∑' j, R i j) := by rw [hL.tsum_comm,hR.tsum_comm]
    _ = ∑' i, ((∑' j, L i j)+(∑' j, R i j)) := (Summable.tsum_add hL.prod hR.prod).symm
    _ = _ := by simp_rw [hLR]; exact hcut'.tsum_eq
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma summable_modulated_product_shift (hc : A.toVertexAlgebra.C2Cofinite)
    {a b : V} {d e : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    {f g : ℤ → ℂ} (hf : RapidCoefficients f) (hg : RapidCoefficients g)
    (r : ℤ) (x : U.smoothEnergySpace) :
    Summable (fun j : ℕ => ((U.smoothSmear hc ha (hg.shift (-(j+r:ℤ))))
      (U.smoothSmear hc hb (hf.shift (j+r:ℤ)) x) : Completion V)) := by
  have H := U.summable_modulated_product hc ha hb (hf.shift r) (hg.shift (-r)) x
  convert! H using 1
  funext j
  congr 4 <;> funext n <;> congr 1 <;> omega

def modulatedSum (hc : A.toVertexAlgebra.C2Cofinite)
    {a b : V} {d e : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    {f g : ℤ → ℂ} (hf : RapidCoefficients f) (hg : RapidCoefficients g)
    (r : ℤ) : U.smoothEnergySpace →ₗ[ℂ] Completion V where
  toFun := fun x => ∑' j : ℕ, ((U.smoothSmear hc ha (hg.shift (-(j+r:ℤ))))
    (U.smoothSmear hc hb (hf.shift (j+r:ℤ)) x) : Completion V)
  map_add' := by
    intro x y
    simp only [map_add,Submodule.coe_add]
    exact Summable.tsum_add (U.summable_modulated_product_shift hc ha hb hf hg r x)
      (U.summable_modulated_product_shift hc ha hb hf hg r y)
  map_smul' := by
    intro c x
    simp only [map_smul,Submodule.coe_smul]
    exact tsum_const_smul'' _

lemma modulatedSum_apply (hc : A.toVertexAlgebra.C2Cofinite)
    {a b : V} {d e : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    {f g : ℤ → ℂ} (hf : RapidCoefficients f) (hg : RapidCoefficients g)
    (r : ℤ) (x : U.smoothEnergySpace) :
    U.modulatedSum hc ha hb hf hg r x = ∑' j : ℕ,
      ((U.smoothSmear hc ha (hg.shift (-(j+r:ℤ))))
        (U.smoothSmear hc hb (hf.shift (j+r:ℤ)) x) : Completion V) := rfl
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
def smoothEnergyPowerLinear (r : ℕ) : U.smoothEnergySpace →ₗ[ℂ] Completion V :=
  (U.energyPower r).toFun.comp
    (Submodule.inclusion (iInf_le (fun k => (U.energyPower k).domain) r))
lemma smoothEnergyPowerLinear_apply (r : ℕ) (x : U.smoothEnergySpace) :
    U.smoothEnergyPowerLinear r x=U.smoothEnergyPower r x := rfl
lemma smoothEnergyPowerLinear_dense (r : ℕ) : DenseRange (U.smoothEnergyPowerLinear r) := by
  apply Completion.denseRange_coe.mono
  rintro z ⟨v,rfl⟩
  refine ⟨U.smoothCoreVector (U.inverseCoreEnergy r v),?_⟩
  rw [U.smoothEnergyPowerLinear_apply,U.smoothEnergyPower_core,U.energyShift_inverseCoreEnergy]
lemma smoothEnergyPower_inverse_add (r s : ℕ) (x : U.smoothEnergySpace) :
    U.inverseSobolev s (U.smoothEnergyPower (r+s) x)=U.smoothEnergyPower r x := by
  apply U.inverseSobolev_injective r
  change (U.inverseSobolev r*U.inverseSobolev s) (U.smoothEnergyPower (r+s) x)=_
  rw [U.inverseSobolev_mul,U.inverseSobolev_smoothEnergyPower,U.inverseSobolev_smoothEnergyPower]
lemma smoothEnergyPower_norm_add (r s : ℕ) (x : U.smoothEnergySpace) :
    ‖U.smoothEnergyPower r x‖ ≤ ‖U.inverseSobolev s‖*‖U.smoothEnergyPower (r+s) x‖ := by
  rw [← U.smoothEnergyPower_inverse_add r s x]
  exact (U.inverseSobolev s).le_opNorm _
 

lemma smooth_linear_eq_of_core (L M : U.smoothEnergySpace →ₗ[ℂ] Completion V)
    (hL : ∃ r : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖L x‖ ≤ C*‖U.smoothEnergyPower r x‖)
    (hM : ∃ s : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ x, ‖M x‖ ≤ D*‖U.smoothEnergyPower s x‖)
    (he : ∀ v : V, L (U.smoothCoreVector v)=M (U.smoothCoreVector v)) : L=M := by
  obtain ⟨r,C,hC,hL⟩ := hL
  obtain ⟨s,D,hD,hM⟩ := hM
  let Q := L-M
  let S := U.smoothEnergyPowerLinear (r+s)
  have hQ (x : U.smoothEnergySpace) : ‖Q x‖ ≤
      (C*‖U.inverseSobolev s‖+D*‖U.inverseSobolev r‖)*‖S x‖ := by
    have h1 := (hL x).trans (mul_le_mul_of_nonneg_left (U.smoothEnergyPower_norm_add r s x) hC)
    have h2 := (hM x).trans (mul_le_mul_of_nonneg_left (U.smoothEnergyPower_norm_add s r x) hD)
    rw [Nat.add_comm s r] at h2
    exact (norm_sub_le (L x) (M x)).trans (by change _ ≤ (C*‖U.inverseSobolev s‖+D*‖U.inverseSobolev r‖)*‖U.smoothEnergyPower (r+s) x‖; nlinarith)
  let B := Q.extendOfNorm S
  have hB (x : U.smoothEnergySpace) : B (S x)=Q x :=
    Q.extendOfNorm_eq (U.smoothEnergyPowerLinear_dense (r+s)) ⟨_,hQ⟩ x
  have hb (v : V) : B (v : Completion V)=0 := by
    have h := hB (U.smoothCoreVector (U.inverseCoreEnergy (r+s) v))
    have hs : S (U.smoothCoreVector (U.inverseCoreEnergy (r+s) v))=(v:Completion V) := by
      dsimp [S]
      rw [U.smoothEnergyPowerLinear_apply,U.smoothEnergyPower_core,U.energyShift_inverseCoreEnergy]
    rw [hs] at h
    simpa only [Q,LinearMap.sub_apply,he,sub_self] using h
  have hzero : B=0 := by
    ext x
    exact Completion.denseRange_coe.induction_on x
      (isClosed_eq B.continuous continuous_const) hb
  ext x
  have h := hB x
  rw [hzero] at h
  exact sub_eq_zero.mp h.symm
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma modulatedSum_sobolev_bound (hc : A.toVertexAlgebra.C2Cofinite)
    {a b : V} {d e : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    {f g : ℤ → ℂ} (hf : RapidCoefficients f) (hg : RapidCoefficients g) (r : ℤ) :
    ∃ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : U.smoothEnergySpace,
      ‖U.modulatedSum hc ha hb hf hg r x‖ ≤ C*‖U.smoothEnergyPower m x‖ := by
  obtain ⟨m,K,hK,h⟩ := U.modulated_product_uniform_bound hc ha hb (hf.shift r) (hg.shift (-r))
  have h' (j : ℕ) (x : U.smoothEnergySpace) :
      ‖(U.smoothSmear hc ha (hg.shift (-(j+r:ℤ)))
        (U.smoothSmear hc hb (hf.shift (j+r:ℤ)) x) : Completion V)‖ ≤
        K/(1+(j:ℝ))^2*‖U.smoothEnergyPower m x‖ := by
    convert! h j x using 1
    congr 5 <;> funext n <;> congr 1 <;> omega
  have hs : Summable (fun j : ℕ => K/(1+(j:ℝ))^2) := by
    have ht := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
    have ht' : Summable (fun j : ℕ => 1/(1+(j:ℝ))^2) := by
      simpa only [Nat.cast_add,Nat.cast_one,add_comm] using ht
    simpa only [mul_one_div] using ht'.mul_left K
  refine ⟨m,∑' j : ℕ, K/(1+(j:ℝ))^2,tsum_nonneg (fun _ => by positivity),?_⟩
  intro x
  rw [U.modulatedSum_apply]
  calc
    _ ≤ ∑' j : ℕ, K/(1+(j:ℝ))^2*‖U.smoothEnergyPower m x‖ :=
      tsum_of_norm_bounded (hs.mul_right _).hasSum (fun j => h' j x)
    _ = _ := tsum_mul_right
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
def localNormalMap (hc : A.toVertexAlgebra.C2Cofinite)
    {a b : V} {d e : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    (f χ : SmoothCircleFunction) (c : ℤ) : U.smoothEnergySpace →ₗ[ℂ] Completion V :=
  U.modulatedSum hc ha hb f.rapid_coefficients χ.rapid_coefficients (1-c)+
  U.modulatedSum hc hb ha χ.rapid_coefficients f.rapid_coefficients c
lemma localNormalMap_matrix (hc : A.toVertexAlgebra.C2Cofinite)
    {a b x y : V} {d e D E : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    (hx : x ∈ A.grade D) (hy : y ∈ A.grade E) (c : ℤ)
    {χ f : SmoothCircleFunction}
    (hχ : Disjoint (tsupport (χ.add (SmoothCircleFunction.constant (-1)))) (tsupport f)) :
    inner ℂ (x:Completion V) (U.localNormalMap hc ha hb f χ c (U.smoothCoreVector y)) =
      f.coefficient ((E:ℤ)-D)*inner ℂ x (A.normalAt a b d e ((E:ℤ)-D) c y) := by
  unfold localNormalMap
  rw [LinearMap.add_apply,inner_add_right,U.modulatedSum_apply,U.modulatedSum_apply,
    inner_tsum_right (U.summable_modulated_product_shift hc ha hb f.rapid_coefficients χ.rapid_coefficients (1-c) _),
    inner_tsum_right (U.summable_modulated_product_shift hc hb ha χ.rapid_coefficients f.rapid_coefficients c _)]
  have h1 (j : ℕ) : -(j+(1-c):ℤ)=c-(j+1:ℤ) := by omega
  have h2 (j : ℕ) : (j+(1-c):ℤ)=(j+1:ℤ)-c := by omega
  simp_rw [h1,h2]
  exact U.local_normal_series_matrix_shift hc ha hb hx hy c hχ
lemma localNormalMap_core (hc : A.toVertexAlgebra.C2Cofinite)
    {a b : V} {d e : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    {χ f : SmoothCircleFunction}
    (hχ : Disjoint (tsupport (χ.add (SmoothCircleFunction.constant (-1)))) (tsupport f)) (y : V) :
    U.localNormalMap hc ha hb f χ (1-(d:ℤ)) (U.smoothCoreVector y)=
      A.smearedMap (mode A.fields a (-1) b) (d+e)
        (U.polynomialEnergyBounds hc _) f.coefficient f.rapid_coefficients y := by
  let L := U.localNormalMap hc ha hb f χ (1-(d:ℤ))
  let M := A.smearedMap (mode A.fields a (-1) b) (d+e)
    (U.polynomialEnergyBounds hc _) f.coefficient f.rapid_coefficients
  have hc0 : U.smoothCoreVector (0:V)=0 := by ext; simp only [smoothCoreVector,Completion.coe_zero,Submodule.coe_zero]
  have hca (v w : V) : U.smoothCoreVector (v+w)=U.smoothCoreVector v+U.smoothCoreVector w := by
    ext; simp only [smoothCoreVector,Completion.coe_add,Submodule.coe_add]
  have hn : mode A.fields a (-1) b ∈ A.grade (d+e) := A.mode_mem_grade ha hb (-1) (by omega)
  change L (U.smoothCoreVector y)=M y
  apply A.homogeneous_induction (P := fun y => L (U.smoothCoreVector y)=M y)
  · simp only [hc0,map_zero]
  · intro E y hy
    apply ext_inner_left ℂ
    intro x
    apply Completion.denseRange_coe.induction_on (p := fun x =>
      inner ℂ x (L (U.smoothCoreVector y))=inner ℂ x (M y)) x
      (isClosed_eq (continuous_id.inner continuous_const) (continuous_id.inner continuous_const))
    intro x
    apply A.homogeneous_induction (P := fun x =>
      inner ℂ (x:Completion V) (L (U.smoothCoreVector y))=inner ℂ (x:Completion V) (M y))
    · simp only [Completion.coe_zero,inner_zero_left]
    · intro D x hx
      exact (U.localNormalMap_matrix hc ha hb hx hy (1-(d:ℤ)) hχ).trans (by
        rw [A.normalAt_vertex_product]
        exact (U.inner_smearedMap_homogeneous hn hx hy _ f.rapid_coefficients).symm)
    · intro x z hx hz
      simp only [Completion.coe_add,inner_add_left,hx,hz]
  · intro y z hy hz
    simp only [hca,map_add,hy,hz]
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma smooth_linear_add_bound (L M : U.smoothEnergySpace →ₗ[ℂ] Completion V)
    (hL : ∃ r : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖L x‖ ≤ C*‖U.smoothEnergyPower r x‖)
    (hM : ∃ s : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ x, ‖M x‖ ≤ D*‖U.smoothEnergyPower s x‖) :
    ∃ r : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖(L+M) x‖ ≤ C*‖U.smoothEnergyPower r x‖ := by
  obtain ⟨r,C,hC,hL⟩ := hL
  obtain ⟨s,D,hD,hM⟩ := hM
  refine ⟨r+s,C*‖U.inverseSobolev s‖+D*‖U.inverseSobolev r‖,by positivity,?_⟩
  intro x
  have h1 := (hL x).trans (mul_le_mul_of_nonneg_left (U.smoothEnergyPower_norm_add r s x) hC)
  have h2 := (hM x).trans (mul_le_mul_of_nonneg_left (U.smoothEnergyPower_norm_add s r x) hD)
  rw [Nat.add_comm s r] at h2
  exact (norm_add_le (L x) (M x)).trans (by nlinarith)
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

end

end OAI
