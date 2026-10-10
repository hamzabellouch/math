import Mathlib
import OAI.RepresentationTheory.VertexAlgebra.SmoothConjugatePrimary

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
namespace StronglyRationalVOA

namespace CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma smoothSmear_shift_bound (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d k p : ℕ} (ha : a ∈ A.grade d) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n v, ‖A.physicalMode a d n v‖ ≤ C*(1+|(n:ℝ)|)^p*‖(A.energyShift^k) v‖)
    {f : ℤ → ℂ} (hf : RapidCoefficients f) (j : ℤ) (x : U.smoothEnergySpace) :
    ‖(U.smoothSmear hc ha (hf.shift j) x : Completion V)‖ ≤
      (coefficientSeminorm f p*C*(1+|(j:ℝ)|)^p)*‖U.smoothEnergyPower k x‖ := by
  rw [U.smoothSmear_eq_normalized hc ha hb (hf.shift j) x]
  calc
    _ ≤ (coefficientSeminorm (fun n => f (n-j)) p*C)*‖U.smoothEnergyPower k x‖ :=
      (U.normalizedField hc a d k (hf.shift j)).le_of_opNorm_le (U.normalizedField_norm hc hC hb (hf.shift j)) _
    _ ≤ _ := by
      have hs := coefficientSeminorm_shift hf j p
      calc
        _ ≤ (coefficientSeminorm f p*(1+|(j:ℝ)|)^p*C)*‖U.smoothEnergyPower k x‖ := by gcongr
        _ = _ := by ring

 

lemma summable_modulated_product (hc : A.toVertexAlgebra.C2Cofinite)
    {a b : V} {d e : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    {f g : ℤ → ℂ} (hf : RapidCoefficients f) (hg : RapidCoefficients g)
    (x : U.smoothEnergySpace) :
    Summable (fun j : ℕ => ((U.smoothSmear hc ha (hg.shift (-(j:ℤ))))
      (U.smoothSmear hc hb (hf.shift (j:ℤ)) x) : Completion V)) := by
  obtain ⟨C,hC,p,k,hA⟩ := (U.polynomialEnergyBounds hc a).physical A d
  obtain ⟨D,hD,q,l,hB⟩ := (U.polynomialEnergyBounds hc b).physical A e
  let R := p+q+k+2
  let K := (coefficientSeminorm g p*C)*(coefficientSeminorm f (q+R+k)*D)*
    ‖U.smoothEnergyPower (l+R+k) x‖
  have hFg := coefficientSeminorm_nonneg g p
  have hFf := coefficientSeminorm_nonneg f (q+R+k)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hs : Summable (fun j : ℕ => K/(1+(j:ℝ))^2) := by
    have ht := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
    have ht' : Summable (fun j : ℕ => 1/(1+(j:ℝ))^2) := by
      simpa only [Nat.cast_add,Nat.cast_one,add_comm] using ht
    simpa only [mul_one_div] using ht'.mul_left K
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hs
  intro j
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
end CFTTypeVOA.UnitaryStructure
end StronglyRationalVOA

namespace StronglyRationalVOA.CFTTypeVOA
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (A : CFTTypeVOA V)
 
def normalAt (a b : V) (d e : ℕ) (k i : ℤ) (v : V) : V :=
  (∑ᶠ j : ℕ, A.physicalMode a d (i-1-j) (A.physicalMode b e (k-i+1+j) v))+
  (∑ᶠ j : ℕ, A.physicalMode b e (k-i-j) (A.physicalMode a d (i+j) v))

lemma normalAt_left_finite (a b : V) (d e : ℕ) (k i : ℤ) (v : V) :
    Function.HasFiniteSupport (fun j : ℕ => A.physicalMode a d (i-1-j)
      (A.physicalMode b e (k-i+1+j) v)) := by
  apply (mode_shift_hasFiniteSupport A.fields b v (k-i+e)).subset
  intro j hj
  change _ ≠ 0 at hj ⊢
  intro hz
  apply hj
  have he : k-i+1+(j:ℤ)+e-1=k-i+e+j := by omega
  simp only [physicalMode,he,hz,map_zero]

lemma normalAt_right_finite (a b : V) (d e : ℕ) (k i : ℤ) (v : V) :
    Function.HasFiniteSupport (fun j : ℕ => A.physicalMode b e (k-i-j)
      (A.physicalMode a d (i+j) v)) := by
  apply (mode_shift_hasFiniteSupport A.fields a v (i+d-1)).subset
  intro j hj
  change _ ≠ 0 at hj ⊢
  intro hz
  apply hj
  have he : i+(j:ℤ)+d-1=i+d-1+j := by omega
  simp only [physicalMode,he,hz,map_zero]

lemma normalAt_step (a b : V) (d e : ℕ) (k i : ℤ) (v : V) :
    A.normalAt a b d e k (i+1) v-A.normalAt a b d e k i v=
      A.physicalMode a d i (A.physicalMode b e (k-i) v)-
      A.physicalMode b e (k-i) (A.physicalMode a d i v) := by
  have hL := finsum_nat_split _ (A.normalAt_left_finite a b d e k (i+1) v) 1
  have hR := finsum_nat_split _ (A.normalAt_right_finite a b d e k i v) 1
  simp only [Finset.sum_range_one,Nat.cast_zero,sub_zero,add_zero,Nat.cast_add,Nat.cast_one] at hL hR
  have hi1 : i+1-1=i := by omega
  have hi2 : k-(i+1)+1=k-i := by omega
  have hj1 (j : ℕ) : i+1-1-(1+(j:ℤ))=i-1-j := by omega
  have hj2 (j : ℕ) : k-(i+1)+1+(1+(j:ℤ))=k-i+1+j := by omega
  have hj3 (j : ℕ) : k-i-(1+(j:ℤ))=k-(i+1)-j := by omega
  have hj4 (j : ℕ) : i+(1+(j:ℤ))=i+1+j := by omega
  simp only [hj1,hj2] at hL
  simp only [hj3,hj4] at hR
  dsimp only [normalAt]
  simp only [hi1,hi2] at hL ⊢
  rw [hL,hR]
  abel

lemma normalAt_vertex_product (a b : V) (d e : ℕ) (k : ℤ) (v : V) :
    A.normalAt a b d e k (1-(d:ℤ)) v=
      A.physicalMode (mode A.fields a (-1) b) (d+e) k v := by
  calc
    _ = ∑ᶠ j : ℕ, (A.physicalMode a d (1-(d:ℤ)-1-j)
        (A.physicalMode b e (k-(1-(d:ℤ))+1+j) v)+
        A.physicalMode b e (k-(1-(d:ℤ))-j) (A.physicalMode a d (1-(d:ℤ)+j) v)) :=
      (finsum_add_distrib (A.normalAt_left_finite a b d e k (1-(d:ℤ)) v)
        (A.normalAt_right_finite a b d e k (1-(d:ℤ)) v)).symm
    _ = _ := by
      rw [physicalMode,A.mode_normal_product]
      apply finsum_congr
      intro j
      simp only [physicalMode,Nat.cast_add]
      have h1 : 1-(d:ℤ)-1-j+d-1 = -1-j := by omega
      have h2 : k-(1-(d:ℤ))+1+j+e-1=k+((d:ℤ)+e)-1+j := by omega
      have h3 : k-(1-(d:ℤ))-j+e-1=k+((d:ℤ)+e)-1-1-j := by omega
      have h4 : 1-(d:ℤ)+j+d-1=j := by omega
      rw [h1,h2,h3,h4]

 

lemma normalAt_choose {a b : V} {d e : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    (k i : ℤ) (v : V) :
    A.normalAt a b d e k i v = A.physicalMode (mode A.fields a (-1) b) (d+e) k v+
      ∑ j ∈ Finset.range (d+e), Ring.choose ((i:ℂ)+d-1) (j+1) •
        mode A.fields (mode A.fields a j b) (k+d+e-2-j) v := by
  let P : ℤ → V := fun i => ∑ j ∈ Finset.range (d+e), Ring.choose ((i:ℂ)+d-1) (j+1) •
    mode A.fields (mode A.fields a j b) (k+d+e-2-j) v
  have hP (i : ℤ) : P (i+1)-P i =
      ∑ j ∈ Finset.range (d+e), Ring.choose ((i:ℂ)+d-1) j •
        mode A.fields (mode A.fields a j b) (k+d+e-2-j) v := by
    dsimp only [P]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [← sub_smul]
    have hi : ((i+1:ℤ):ℂ)+d-1=((i:ℂ)+d-1)+1 := by push_cast; ring
    rw [hi,Ring.choose_succ_succ,add_sub_cancel_right]
  let F : ℤ → V := fun i => A.normalAt a b d e k i v-P i
  have hF (i : ℤ) : F (i+1)=F i := by
    have h := A.normalAt_step a b d e k i v
    rw [A.physicalMode_commutator_finite ha hb] at h
    have he : i+(k-i)+(d:ℤ)+e-2=k+d+e-2 := by omega
    simp only [he] at h
    have hp := hP i
    dsimp only [F]
    exact (sub_eq_sub_iff_sub_eq_sub.mpr (h.trans hp.symm))
  have hc (i : ℤ) : F i=F 0 := by
    induction i using Int.induction_on with
    | zero => rfl
    | succ n ih => exact (hF n).trans ih
    | pred n ih =>
      have hi : (-(n:ℤ)-1)+1=-(n:ℤ) := by omega
      have hh := hF (-(n:ℤ)-1)
      rw [hi] at hh
      exact hh.symm.trans ih
  have he := (hc i).trans (hc (1-(d:ℤ))).symm
  have hz : P (1-(d:ℤ))=0 := by
    dsimp only [P]
    have hi : ((1-(d:ℤ):ℤ):ℂ)+d-1=0 := by push_cast; ring
    simp only [hi,Ring.choose_zero_succ,zero_smul,Finset.sum_const_zero]
  dsimp only [F] at he
  rw [hz,sub_zero,A.normalAt_vertex_product] at he
  exact sub_eq_iff_eq_add.mp he

end StronglyRationalVOA.CFTTypeVOA

open UniformSpace
namespace StronglyRationalVOA.SmoothCircleFunction
 

lemma hasSum_choose_cutoff {χ f : SmoothCircleFunction}
    (hχ : Disjoint (tsupport (χ.add (constant (-1)))) (tsupport f))
    (c : ℂ) (j : ℕ) (k : ℤ) :
    HasSum (fun i : ℤ => Ring.choose ((i:ℂ)+c) j*χ.coefficient i*f.coefficient (k-i))
      (Ring.choose c j*f.coefficient k) := by
  have H := hasSum_choose_convolution_zero hχ c j k
  have hd : HasSum (fun i : ℤ => if i=0 then Ring.choose c j*f.coefficient k else 0)
      (Ring.choose c j*f.coefficient k) := hasSum_ite_eq 0 _
  have he (i : ℤ) : Ring.choose ((i:ℂ)+c) j*χ.coefficient i*f.coefficient (k-i)=
      Ring.choose ((i:ℂ)+c) j*(χ.add (constant (-1))).coefficient i*f.coefficient (k-i)+
        (if i=0 then Ring.choose c j*f.coefficient k else 0) := by
    rw [coefficient_add,coefficient_constant]
    split_ifs with hi
    · subst i; simp only [Int.cast_zero,zero_add,sub_zero]; ring
    · ring
  simpa only [he,zero_add] using H.add hd
end StronglyRationalVOA.SmoothCircleFunction
namespace StronglyRationalVOA.CFTTypeVOA
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (A : CFTTypeVOA V)
 

lemma hasSum_normalAt_cutoff {a b : V} {d e : ℕ}
    (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    {χ f : SmoothCircleFunction}
    (hχ : Disjoint (tsupport (χ.add (SmoothCircleFunction.constant (-1)))) (tsupport f))
    (k : ℤ) (v : V) :
    HasSum (fun i : ℤ => (χ.coefficient i*f.coefficient (k-i)) •
      (A.normalAt a b d e k i v : Completion V))
      (f.coefficient k • (A.normalAt a b d e k 0 v : Completion V)) := by
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
  have Hj (j : ℕ) := (SmoothCircleFunction.hasSum_choose_cutoff hχ ((d:ℂ)-1) (j+1) k).smul_const (w j)
  have H := H0.add (hasSum_sum (s := Finset.range (d+e)) (fun j _ => Hj j))
  have he (i : ℤ) : (χ.coefficient i*f.coefficient (k-i)) •
      (A.normalAt a b d e k i v : Completion V)=
      (χ.coefficient i*f.coefficient (k-i)) • z+
        ∑ j ∈ Finset.range (d+e),
          (Ring.choose ((i:ℂ)+((d:ℂ)-1)) (j+1)*χ.coefficient i*f.coefficient (k-i)) • w j := by
    rw [A.normalAt_choose ha hb]
    simp only [Completion.coe_add,hs,Completion.coe_smul,smul_add,Finset.smul_sum,smul_smul]
    apply congrArg₂ (· + ·) rfl
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [w]
    congr 1
    rw [show (i:ℂ)+d-1=(i:ℂ)+((d:ℂ)-1) by ring]
    ring
  have hz : f.coefficient k • (A.normalAt a b d e k 0 v : Completion V)=
      f.coefficient k • z+∑ j ∈ Finset.range (d+e),
        (Ring.choose ((d:ℂ)-1) (j+1)*f.coefficient k) • w j := by
    rw [A.normalAt_choose ha hb]
    simp only [Int.cast_zero,zero_add,Completion.coe_add,hs,Completion.coe_smul,
      smul_add,Finset.smul_sum,smul_smul]
    apply congrArg₂ (· + ·) rfl
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [w]
    rw [mul_comm]
  rw [hz]
  convert H using 1
  exact funext he
end StronglyRationalVOA.CFTTypeVOA

open UniformSpace
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
def smoothCoreVector (v : V) : U.smoothEnergySpace :=
  ⟨(v:Completion V),U.core_le_smoothEnergySpace (HilbertCore.equiv V v).property⟩
lemma smoothEnergyPower_core (r : ℕ) (v : V) :
    U.smoothEnergyPower r (U.smoothCoreVector v)=((A.energyShift^r) v : Completion V) :=
  U.energyPower_coe r v
lemma hasSum_smoothSmear_product_core (hc : A.toVertexAlgebra.C2Cofinite)
    {a b : V} {d e : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    {f g : ℤ → ℂ} (hf : RapidCoefficients f) (hg : RapidCoefficients g) (y : V) :
    HasSum (fun n : ℤ => g n •
      (U.smoothSmear hc ha hf (U.smoothCoreVector (A.physicalMode b e n y)) : Completion V))
      (U.smoothSmear hc ha hf (U.smoothSmear hc hb hg (U.smoothCoreVector y)) : Completion V) := by
  obtain ⟨C,_,p,k,hA⟩ := (U.polynomialEnergyBounds hc a).physical A d
  have H := (U.normalizedField hc a d k hf).hasSum
    (U.summable_norm_sobolevSmear hb (U.polynomialEnergyBounds hc b) hg k y).of_norm.hasSum
  have he : U.smoothEnergyPower k (U.smoothSmear hc hb hg (U.smoothCoreVector y))=
      ∑' n : ℤ, g n • ((A.energyShift^k) (A.physicalMode b e n y) : Completion V) := by
    apply (U.energyPower k).mem_graph_snd_inj (U.smoothEnergyPower_graph k _)
      (U.smearedMap_energyGraph hb (U.polynomialEnergyBounds hc b) hg k y)
    exact U.smoothSmear_coe hc hb hg y
  rw [U.smoothSmear_eq_normalized hc ha hA hf,he]
  convert H using 1
  funext n
  rw [map_smul,U.smoothSmear_eq_normalized hc ha hA hf,U.smoothEnergyPower_core]

 

lemma hasSum_smoothSmear_product_matrix (hc : A.toVertexAlgebra.C2Cofinite)
    {a b x y : V} {d e D E : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    (hx : x ∈ A.grade D) (hy : y ∈ A.grade E)
    {f g : ℤ → ℂ} (hf : RapidCoefficients f) (hg : RapidCoefficients g) :
    HasSum (fun n : ℤ => f ((E:ℤ)-D-n)*g n*
      inner ℂ x (A.physicalMode a d ((E:ℤ)-D-n) (A.physicalMode b e n y)))
      (inner ℂ (x : Completion V)
        (U.smoothSmear hc ha hf (U.smoothSmear hc hb hg (U.smoothCoreVector y)) : Completion V)) := by
  have H := (innerSL ℂ (x : Completion V)).hasSum (U.hasSum_smoothSmear_product_core hc ha hb hf hg y)
  convert! H using 1
  funext n
  change _ = inner ℂ (x : Completion V) (g n •
    (U.smoothSmear hc ha hf (U.smoothCoreVector (A.physicalMode b e n y)) : Completion V))
  dsimp only [smoothCoreVector]
  rw [inner_smul_right,U.smoothSmear_coe]
  by_cases hn : (E:ℤ) < n
  · have hz : A.physicalMode b e n y=0 := A.mode_eq_zero_of_negative_energy hb hy _ (by omega)
    simp only [hz,map_zero,inner_zero_right,mul_zero]
  · have hgrade : A.physicalMode b e n y ∈ A.grade ((E:ℤ)-n).toNat :=
      A.mode_mem_grade hb hy _ (by omega)
    have he : (((E:ℤ)-n).toNat : ℤ)-D=(E:ℤ)-D-n := by omega
    rw [U.inner_smearedMap_homogeneous ha hx hgrade,he]
    ring
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

namespace StronglyRationalVOA
 

lemma summable_norm_normal_triangle {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    {F : ℤ → H} {K : ℝ} (hK : 0 ≤ K) (P N : ℕ)
    (hF : ∀ r, ‖F r‖ ≤ K*(1+|(r:ℝ)|)^P)
    (hz : ∀ r, r < -(N:ℤ) → F r=0)
    {f g : ℤ → ℂ} (hf : RapidCoefficients f) (hg : RapidCoefficients g) (k : ℤ) :
    Summable (fun q : ℤ × ℕ => ‖(f q.1*g (k-q.1)) • F (q.1-1-q.2)‖) := by
  let G := coefficientSeminorm g 0
  have hG : 0 ≤ G := coefficientSeminorm_nonneg g 0
  have hgB (i : ℤ) : ‖g i‖ ≤ G := by
    have h := (hg 0).le_tsum i (fun n _ => by positivity)
    simpa only [G,coefficientSeminorm,pow_zero,mul_one] using h
  let C := K*G*(N+2 : ℝ)^(P+2)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hj : Summable (fun j : ℕ => C/(1+(j:ℝ))^2) := by
    have h := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
    have h' : Summable (fun j : ℕ => 1/(1+(j:ℝ))^2) := by
      simpa only [Nat.cast_add,Nat.cast_one,add_comm] using h
    simpa only [mul_one_div] using h'.mul_left C
  have hs := (hf (P+2)).mul_of_nonneg hj (fun _ => by positivity) (fun _ => by positivity)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hs
  rintro ⟨i,j⟩
  change ‖(f i*g (k-i)) • F (i-1-j)‖ ≤
    (‖f i‖*(1+|(i:ℝ)|)^(P+2))*(C/(1+(j:ℝ))^2)
  by_cases hr : i-1-(j:ℤ) < -(N:ℤ)
  · rw [hz _ hr,smul_zero,norm_zero]
    positivity
  · have hlow : -(N:ℝ) ≤ (i:ℝ)-1-j := by exact_mod_cast (show -(N:ℤ) ≤ i-1-j by omega)
    have hjbound : 1+(j:ℝ) ≤ (N+2 : ℝ)*(1+|(i:ℝ)|) := by
      have hi := le_abs_self (i:ℝ)
      have hNi : 0 ≤ (N:ℝ)*|(i:ℝ)| := by positivity
      nlinarith
    have hrabs : |((i-1-(j:ℤ):ℤ):ℝ)| ≤ |(i:ℝ)|+(N:ℝ)+1 := by
      rw [Int.cast_sub,Int.cast_sub,Int.cast_one,Int.cast_natCast]
      apply abs_le.mpr
      constructor
      · linarith [abs_nonneg (i:ℝ)]
      · linarith [le_abs_self (i:ℝ),Nat.cast_nonneg (α := ℝ) j,Nat.cast_nonneg (α := ℝ) N]
    have hrbound : 1+|((i-1-(j:ℤ):ℤ):ℝ)| ≤ (N+2 : ℝ)*(1+|(i:ℝ)|) := by
      have hNi : 0 ≤ (N:ℝ)*|(i:ℝ)| := by positivity
      nlinarith [abs_nonneg (i:ℝ)]
    have hd : 0 < (1+(j:ℝ))^2 := by positivity
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hd).mpr
    calc
      ‖(f i*g (k-i)) • F (i-1-j)‖*(1+(j:ℝ))^2 ≤
          (‖f i‖*G*(K*((N+2 : ℝ)*(1+|(i:ℝ)|))^P))*
            ((N+2 : ℝ)*(1+|(i:ℝ)|))^2 := by
        rw [norm_smul,norm_mul]
        gcongr
        · exact hgB _
        · exact (hF _).trans (by gcongr)
      _ = (‖f i‖*(1+|(i:ℝ)|)^(P+2))*C := by
        dsimp only [C]
        simp only [pow_add,mul_pow]
        ring
end StronglyRationalVOA

open UniformSpace
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
include U in
lemma normal_diagonal_polynomial_bound (hc : A.toVertexAlgebra.C2Cofinite)
    {a b : V} {d e : ℕ} (_ha : a ∈ A.grade d) (hb : b ∈ A.grade e) (k : ℤ) (y : V) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ P : ℕ, ∀ r : ℤ,
      ‖A.physicalMode a d r (A.physicalMode b e (k-r) y)‖ ≤ K*(1+|(r:ℝ)|)^P := by
  obtain ⟨C,hC,p,l,hA⟩ := (U.polynomialEnergyBounds hc a).physical A d
  obtain ⟨D,hD,q,m,hB⟩ := (U.polynomialEnergyBounds hc b).physical A e
  refine ⟨C*D*(1+|(k:ℝ)|)^(q+l)*‖(A.energyShift^(m+l)) y‖,by positivity,p+(q+l),?_⟩
  intro r
  have hkr : 1+|((k-r:ℤ):ℝ)| ≤ (1+|(k:ℝ)|)*(1+|(r:ℝ)|) := by
    rw [Int.cast_sub]
    have hab : |(k:ℝ)-(r:ℝ)| ≤ |(k:ℝ)|+|(r:ℝ)| := by
      simpa only [sub_eq_add_neg,abs_neg] using abs_add_le (k:ℝ) (-(r:ℝ))
    nlinarith [mul_nonneg (abs_nonneg (k:ℝ)) (abs_nonneg (r:ℝ))]
  calc
    _ ≤ C*(1+|(r:ℝ)|)^p*‖(A.energyShift^l) (A.physicalMode b e (k-r) y)‖ := hA r _
    _ ≤ C*(1+|(r:ℝ)|)^p*(D*(1+|((k-r:ℤ):ℝ)|)^(q+l)*‖(A.energyShift^(m+l)) y‖) := by
      gcongr
      exact U.physicalMode_sobolev_bound hb hD.le hB l (k-r) y
    _ ≤ C*(1+|(r:ℝ)|)^p*(D*((1+|(k:ℝ)|)*(1+|(r:ℝ)|))^(q+l)*‖(A.energyShift^(m+l)) y‖) := by gcongr
    _ = _ := by simp only [pow_add,mul_pow]; ring

include U in
lemma summable_norm_normal_left (hc : A.toVertexAlgebra.C2Cofinite)
    {a b y : V} {d e E : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    (hy : y ∈ A.grade E) (D : ℕ)
    {f g : ℤ → ℂ} (hf : RapidCoefficients f) (hg : RapidCoefficients g) :
    Summable (fun q : ℤ × ℕ => ‖(f q.1*g ((E:ℤ)-D-q.1)) •
      (A.physicalMode a d (q.1-1-q.2)
        (A.physicalMode b e ((E:ℤ)-D-q.1+1+q.2) y) : Completion V)‖) := by
  obtain ⟨K,hK,P,hF⟩ := U.normal_diagonal_polynomial_bound hc ha hb ((E:ℤ)-D) y
  have H := summable_norm_normal_triangle (F := fun r : ℤ =>
      (A.physicalMode a d r (A.physicalMode b e ((E:ℤ)-D-r) y) : Completion V))
    hK P D (fun r => by simpa only [Completion.norm_coe] using hF r)
    (fun r hr => by
      have hz : A.physicalMode b e ((E:ℤ)-D-r) y=0 :=
        A.mode_eq_zero_of_negative_energy hb hy _ (by omega)
      simp only [hz,map_zero,Completion.coe_zero]) hf hg ((E:ℤ)-D)
  convert! H using 1
  funext q
  have he : (E:ℤ)-D-(q.1-1-q.2)=(E:ℤ)-D-q.1+1+q.2 := by omega
  rw [he]

include U in
lemma summable_norm_normal_right (hc : A.toVertexAlgebra.C2Cofinite)
    {a b y : V} {d e E : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    (hy : y ∈ A.grade E) (D : ℕ)
    {f g : ℤ → ℂ} (hf : RapidCoefficients f) (hg : RapidCoefficients g) :
    Summable (fun q : ℤ × ℕ => ‖(f q.1*g ((E:ℤ)-D-q.1)) •
      (A.physicalMode b e ((E:ℤ)-D-q.1-q.2)
        (A.physicalMode a d (q.1+q.2) y) : Completion V)‖) := by
  obtain ⟨K,hK,P,hF⟩ := U.normal_diagonal_polynomial_bound hc hb ha ((E:ℤ)-D) y
  have H := summable_norm_normal_triangle (F := fun r : ℤ =>
      (A.physicalMode b e r (A.physicalMode a d ((E:ℤ)-D-r) y) : Completion V))
    hK P D (fun r => by simpa only [Completion.norm_coe] using hF r)
    (fun r hr => by
      have hz : A.physicalMode a d ((E:ℤ)-D-r) y=0 :=
        A.mode_eq_zero_of_negative_energy ha hy _ (by omega)
      simp only [hz,map_zero,Completion.coe_zero]) (hg.shift 1) hf ((E:ℤ)-D+1)
  let σ : ℤ × ℕ ≃ ℤ × ℕ := Equiv.prodCongr (Equiv.subLeft ((E:ℤ)-D+1)) (Equiv.refl ℕ)
  have H' := H.comp_injective σ.injective
  convert! H' using 1
  funext q
  simp only [Function.comp_apply,σ,Equiv.prodCongr_apply,Prod.map,Equiv.subLeft_apply,Equiv.refl_apply]
  have h1 : (E:ℤ)-D+1-q.1-1=(E:ℤ)-D-q.1 := by omega
  have h2 : (E:ℤ)-D+1-((E:ℤ)-D+1-q.1)=q.1 := by omega
  have h3 : (E:ℤ)-D-((E:ℤ)-D+1-q.1-1-q.2)=q.1+q.2 := by omega
  rw [h3,h1,h2,mul_comm]
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma hasSum_modulated_left_matrix (hc : A.toVertexAlgebra.C2Cofinite)
    {a b x y : V} {d e D E : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    (hx : x ∈ A.grade D) (hy : y ∈ A.grade E)
    {f g : ℤ → ℂ} (hf : RapidCoefficients f) (hg : RapidCoefficients g) (j : ℕ) :
    HasSum (fun i : ℤ => f i*g ((E:ℤ)-D-i)*
      inner ℂ x (A.physicalMode a d (i-1-j) (A.physicalMode b e ((E:ℤ)-D-i+1+j) y)))
      (inner ℂ (x:Completion V) (U.smoothSmear hc ha (hf.shift (-(j+1:ℤ)))
        (U.smoothSmear hc hb (hg.shift (j+1:ℤ)) (U.smoothCoreVector y)) : Completion V)) := by
  have H := U.hasSum_smoothSmear_product_matrix hc ha hb hx hy
    (hf.shift (-(j+1:ℤ))) (hg.shift (j+1:ℤ))
  have H' := (Equiv.subLeft ((E:ℤ)-D+j+1)).hasSum_iff.mpr H
  convert! H' using 1
  funext i
  simp only [Function.comp_apply,Equiv.subLeft_apply]
  have h1 : (E:ℤ)-D-((E:ℤ)-D+j+1-i)-(-(j+1))=i := by omega
  have h2 : (E:ℤ)-D+j+1-i-(j+1)=(E:ℤ)-D-i := by omega
  have h3 : (E:ℤ)-D-((E:ℤ)-D+j+1-i)=i-1-j := by omega
  have h4 : (E:ℤ)-D+j+1-i=(E:ℤ)-D-i+1+j := by omega
  rw [h1,h2,h3,h4]

lemma hasSum_modulated_right_matrix (hc : A.toVertexAlgebra.C2Cofinite)
    {a b x y : V} {d e D E : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    (hx : x ∈ A.grade D) (hy : y ∈ A.grade E)
    {f g : ℤ → ℂ} (hf : RapidCoefficients f) (hg : RapidCoefficients g) (j : ℕ) :
    HasSum (fun i : ℤ => f i*g ((E:ℤ)-D-i)*
      inner ℂ x (A.physicalMode b e ((E:ℤ)-D-i-j) (A.physicalMode a d (i+j) y)))
      (inner ℂ (x:Completion V) (U.smoothSmear hc hb (hg.shift (-(j:ℤ)))
        (U.smoothSmear hc ha (hf.shift (j:ℤ)) (U.smoothCoreVector y)) : Completion V)) := by
  have H := U.hasSum_smoothSmear_product_matrix hc hb ha hx hy (hg.shift (-(j:ℤ))) (hf.shift (j:ℤ))
  have H' := (Equiv.addRight (j:ℤ)).hasSum_iff.mpr H
  convert! H' using 1
  funext i
  simp only [Function.comp_apply,Equiv.coe_addRight]
  have h1 : (E:ℤ)-D-(i+j)-(-(j:ℤ))=(E:ℤ)-D-i := by omega
  have h2 : i+(j:ℤ)-j=i := by omega
  have h3 : (E:ℤ)-D-(i+j)=(E:ℤ)-D-i-j := by omega
  rw [h1,h2,h3,mul_comm (g _) (f _)]
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace
namespace StronglyRationalVOA.CFTTypeVOA
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (A : CFTTypeVOA V)
lemma hasSum_normalAt_completion (a b : V) (d e : ℕ) (k i : ℤ) (v : V) :
    HasSum (fun j : ℕ =>
      (A.physicalMode a d (i-1-j) (A.physicalMode b e (k-i+1+j) v) : Completion V)+
      (A.physicalMode b e (k-i-j) (A.physicalMode a d (i+j) v) : Completion V))
      (A.normalAt a b d e k i v : Completion V) := by
  let Q : V →+ Completion V := (Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V).toLinearMap.toAddMonoidHom
  have hL := A.normalAt_left_finite a b d e k i v
  have hR := A.normalAt_right_finite a b d e k i v
  have hs (F : ℕ → V) (hF : Function.HasFiniteSupport F) :
      HasSum (fun j => Q (F j)) (Q (∑ᶠ j, F j)) := by
    have hQ : Function.HasFiniteSupport (fun j => Q (F j)) := hF.subset (by
      intro j hj hz
      exact hj (by change Q (F j)=0; rw [hz,map_zero]))
    have H : HasSum (fun j => Q (F j)) (∑' j, Q (F j)) :=
      (summable_of_hasFiniteSupport hQ).hasSum
    rw [tsum_eq_finsum hQ,← Q.map_finsum hF] at H
    exact H
  have hQ (w : V) : Q w=(w : Completion V) := rfl
  simpa only [hQ,normalAt,Completion.coe_add] using (hs _ hL).add (hs _ hR)
end StronglyRationalVOA.CFTTypeVOA

open UniformSpace
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

end

end OAI
