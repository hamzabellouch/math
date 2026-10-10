import Mathlib
import OAI.RepresentationTheory.VertexAlgebra.GraphEquiv

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
universe u
open scoped Topology
open Filter
namespace StronglyRationalVOA

namespace HilbertScale
open scoped ENNReal
variable {ι : Type*} {G : ι → Type u} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)] [DecidableEq ι] [∀ i, CompleteSpace (G i)]
theorem boundedMultiplier_single (w : ι → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hw : ∀ i, ‖w i‖ ≤ C) (i : ι) (x : G i) :
    boundedMultiplier w hC hw (lp.single 2 i x) = w i • lp.single 2 i x := by
  ext j
  simp only [boundedMultiplier_apply,lp.coeFn_smul,Pi.smul_apply]
  by_cases hj : j = i
  · subst j; simp
  · simp [lp.single_apply,hj]

theorem boundedMultiplier_preservesFiniteCore (w : ι → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hw : ∀ i, ‖w i‖ ≤ C) :
    ∀ x ∈ finiteCore (G := G), boundedMultiplier w hC hw x ∈ finiteCore := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i,v,rfl⟩ := hx
    rw [boundedMultiplier_single]
    exact Submodule.smul_mem _ _ (single_mem_finiteCore _ _)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

omit [DecidableEq ι] in
theorem boundedMultiplier_graph (w : ι → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hw : ∀ i, ‖w i‖ ≤ C) (x : Space G) :
    (x,boundedMultiplier w hC hw x) ∈ (diagonal w).graph := by
  exact (mem_graph_iff _ _ _).mpr (fun _ => rfl)

omit [DecidableEq ι] in
theorem boundedMultiplier_adjoint (w : ι → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hw : ∀ i, ‖w i‖ ≤ C) :
    (boundedMultiplier (G := G) w hC hw).adjoint =
      boundedMultiplier (fun i => star (w i)) hC (fun i => by simpa using hw i) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right,
    ← (lp.hasSum_inner (boundedMultiplier w hC hw y) x).tsum_eq,
    ← (lp.hasSum_inner y (boundedMultiplier (fun i => star (w i)) hC
      (fun i => by simpa using hw i) x)).tsum_eq]
  apply tsum_congr
  intro i
  simp only [boundedMultiplier_apply,inner_smul_left,inner_smul_right,starRingEnd_apply]

omit [DecidableEq ι] in
theorem real_boundedMultiplier_selfAdjoint (w : ι → ℝ) {C : ℝ}
    (hC : 0 ≤ C) (hw : ∀ i, ‖(w i : ℂ)‖ ≤ C) :
    IsSelfAdjoint (boundedMultiplier (G := G) (fun i => (w i : ℂ)) hC hw) := by
  change (boundedMultiplier (G := G) (fun i => (w i : ℂ)) hC hw).adjoint =
    boundedMultiplier (G := G) (fun i => (w i : ℂ)) hC hw
  rw [boundedMultiplier_adjoint]
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext i
  simp only [boundedMultiplier_apply,Complex.star_def,Complex.conj_ofReal]

omit [∀ (i : ι), CompleteSpace (G i)] in
theorem finiteCore_dense : Dense (finiteCore (G := G) : Set (Space G)) := by
  intro x
  apply mem_closure_of_tendsto (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) x)
  apply Filter.Eventually.of_forall
  intro s
  exact Submodule.sum_mem _ (fun i _ => single_mem_finiteCore i (x i))

end HilbertScale

namespace StrongOperatorLimit
open Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

 

theorem zero_of_dense {S : Submodule ℂ H} (hS : Dense (S : Set H))
    (B : ℕ → H →L[ℂ] H) {C : ℝ} (hC : 0 ≤ C) (hB : ∀ n, ‖B n‖ ≤ C)
    (hlim : ∀ x ∈ S, Tendsto (fun n => B n x) atTop (𝓝 0)) (x : H) :
    Tendsto (fun n => B n x) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨y,hy,hxy⟩ := hS.exists_dist_lt x (show 0 < ε/(2*(C+1)) by positivity)
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp (hlim y hy) (ε/2) (by positivity)
  refine ⟨N,fun n hn => ?_⟩
  have hyb : ‖B n y‖ < ε/2 := by simpa using hN n hn
  have hxy' : ‖x-y‖*(2*(C+1)) < ε := by
    rw [dist_eq_norm] at hxy
    exact (lt_div_iff₀ (by positivity)).mp hxy
  rw [dist_zero_right]
  calc
    ‖B n x‖ = ‖B n (x-y) + B n y‖ := by rw [map_sub,sub_add_cancel]
    _ ≤ ‖B n (x-y)‖ + ‖B n y‖ := norm_add_le _ _
    _ ≤ C*‖x-y‖ + ‖B n y‖ := add_le_add ((B n).le_of_opNorm_le (hB n) _) le_rfl
    _ < ε := by nlinarith [norm_nonneg (x-y)]

end StrongOperatorLimit

namespace HilbertScale
open Filter
open scoped Topology
variable {ι : Type*} {G : ι → Type u} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)] [DecidableEq ι] [∀ i, CompleteSpace (G i)]

 
theorem boundedMultiplier_strong_zero (w : ℕ → ι → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hw : ∀ n i, ‖w n i‖ ≤ C)
    (hlim : ∀ i, Tendsto (fun n => w n i) atTop (𝓝 0)) (x : Space G) :
    Tendsto (fun n => boundedMultiplier (w n) hC (hw n) x) atTop (𝓝 0) := by
  refine StrongOperatorLimit.zero_of_dense (S := finiteCore (G := G)) finiteCore_dense
    (fun n => boundedMultiplier (w n) hC (hw n)) hC
    (fun n => boundedMultiplier_norm (G := G) (w n) hC (hw n)) ?_ x
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i,v,rfl⟩ := hy
    simp only [boundedMultiplier_single]
    simpa only [zero_smul] using (hlim i).smul (tendsto_const_nhds (x := lp.single 2 i v))
  | zero => simpa only [map_zero] using (tendsto_const_nhds (x := (0 : Space G)))
  | add y z _ _ hy hz => simpa only [map_add,zero_add] using hy.add hz
  | smul c y _ hy => simpa only [map_smul,smul_zero] using hy.const_smul c

end HilbertScale
end StronglyRationalVOA

namespace StronglyRationalVOA.HilbertScale
open Filter
open scoped Topology
variable {ι : Type*} {G : ι → Type u} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)] [instDec : DecidableEq ι]

def coreDiagonal (w : ι → ℂ) : finiteCore (G := G) →ₗ[ℂ] Space G :=
  (diagonal w).toFun.comp (Submodule.inclusion (finiteCore_le_domain w))

@[simp] theorem coreDiagonal_apply (w : ι → ℂ) (x : finiteCore (G := G)) (i : ι) :
    coreDiagonal w x i = w i • (x : Space G) i := rfl

@[simp] theorem coreDiagonal_single (w : ι → ℂ) (i : ι) (v : G i) :
    coreDiagonal w ⟨lp.single 2 i v,single_mem_finiteCore i v⟩ = lp.single 2 i (w i • v) :=
  diagonal_single w i v

theorem coreDiagonal_mem_finiteCore (w : ι → ℂ) (x : finiteCore (G := G)) :
    coreDiagonal w x ∈ finiteCore := by
  obtain ⟨x,hx⟩ := x
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i,v,rfl⟩ := hx
    rw [coreDiagonal_single]
    exact single_mem_finiteCore i _
  | zero =>
    change coreDiagonal w 0 ∈ finiteCore (G := G)
    rw [map_zero]
    exact Submodule.zero_mem _
  | add x y hx hy ihx ihy =>
    change coreDiagonal w (⟨x,hx⟩+⟨y,hy⟩) ∈ finiteCore
    rw [map_add]
    exact Submodule.add_mem _ ihx ihy
  | smul c x hx ih =>
    change coreDiagonal w (c • ⟨x,hx⟩) ∈ finiteCore
    rw [map_smul]
    exact Submodule.smul_mem _ c ih

def coreMultiplier (w : ι → ℂ) : finiteCore (G := G) →ₗ[ℂ] finiteCore (G := G) :=
  (coreDiagonal (G := G) w).codRestrict (finiteCore (G := G)) (coreDiagonal_mem_finiteCore w)

@[simp] theorem coreMultiplier_coe (w : ι → ℂ) (x : finiteCore (G := G)) :
    (coreMultiplier w x : Space G) = coreDiagonal w x := rfl

@[simp] theorem coreMultiplier_apply (w : ι → ℂ) (x : finiteCore (G := G)) (i : ι) :
    (coreMultiplier w x : Space G) i = w i • (x : Space G) i := rfl

theorem coreMultiplier_mul (w v : ι → ℂ) (x : finiteCore (G := G)) :
    coreMultiplier w (coreMultiplier v x) = coreMultiplier (fun i => w i*v i) x := by
  apply Subtype.ext
  apply lp.ext
  funext i
  simp only [coreMultiplier_apply,mul_smul]

theorem coreMultiplier_one (x : finiteCore (G := G)) :
    coreMultiplier (fun _ => 1) x = x := by
  apply Subtype.ext
  apply lp.ext
  funext i
  simp only [coreMultiplier_apply,one_smul]

variable [∀ i, CompleteSpace (G i)]

theorem coreMultiplier_eq_bounded (w : ι → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hw : ∀ i, ‖w i‖ ≤ C) (x : finiteCore (G := G)) :
    (coreMultiplier w x : Space G) = boundedMultiplier w hC hw x := rfl

omit [DecidableEq ι]

noncomputable def resolventWeight (h : ι → ℝ) (n : ℕ) (i : ι) : ℝ :=
  ((n : ℝ)+1)/((n : ℝ)+1+h i)

noncomputable def complementWeight (h : ι → ℝ) (n : ℕ) (i : ι) : ℝ :=
  h i/((n : ℝ)+1+h i)

theorem resolventWeight_nonneg (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i) (n : ℕ) (i : ι) :
    0 ≤ resolventWeight h n i := by
  unfold resolventWeight
  have := hh i
  positivity

theorem resolventWeight_le_one (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i) (n : ℕ) (i : ι) :
    resolventWeight h n i ≤ 1 := by
  unfold resolventWeight
  have := hh i
  apply (div_le_one (by positivity)).mpr
  linarith

theorem complementWeight_nonneg (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i) (n : ℕ) (i : ι) :
    0 ≤ complementWeight h n i := by
  unfold complementWeight
  have := hh i
  positivity

theorem complementWeight_le_one (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i) (n : ℕ) (i : ι) :
    complementWeight h n i ≤ 1 := by
  unfold complementWeight
  have := hh i
  apply (div_le_one (by positivity)).mpr
  have hh0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

theorem resolventWeight_add_complementWeight (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i)
    (n : ℕ) (i : ι) : resolventWeight h n i + complementWeight h n i = 1 := by
  unfold resolventWeight complementWeight
  have := hh i
  rw [← add_div,div_self (by positivity)]

theorem complementWeight_tendsto_zero (h : ι → ℝ) (i : ι) :
    Tendsto (fun n => complementWeight h n i) atTop (𝓝 0) := by
  apply Tendsto.const_div_atTop
  exact tendsto_atTop_add_const_right atTop (h i)
    (tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop (R := ℝ)))

omit [DecidableEq ι] in
def resolvent (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i) (n : ℕ) : Space G →L[ℂ] Space G :=
  boundedMultiplier (fun i => (resolventWeight h n i : ℂ)) zero_le_one (fun i => by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (resolventWeight_nonneg h hh n i)]
    exact resolventWeight_le_one h hh n i)

omit [DecidableEq ι] in
def complement (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i) (n : ℕ) : Space G →L[ℂ] Space G :=
  boundedMultiplier (fun i => (complementWeight h n i : ℂ)) zero_le_one (fun i => by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (complementWeight_nonneg h hh n i)]
    exact complementWeight_le_one h hh n i)

@[simp] theorem resolvent_apply (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i) (n : ℕ)
    (x : Space G) (i : ι) : resolvent h hh n x i = (resolventWeight h n i : ℂ) • x i := rfl

@[simp] theorem complement_apply (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i) (n : ℕ)
    (x : Space G) (i : ι) : complement h hh n x i = (complementWeight h n i : ℂ) • x i := rfl

theorem resolvent_add_complement (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i) (n : ℕ) (x : Space G) :
    resolvent h hh n x + complement h hh n x = x := by
  apply lp.ext
  funext i
  change (resolventWeight h n i : ℂ) • x i + (complementWeight h n i : ℂ) • x i = x i
  rw [← add_smul,← Complex.ofReal_add,resolventWeight_add_complementWeight h hh,Complex.ofReal_one,one_smul]

theorem resolvent_selfAdjoint (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i) (n : ℕ) :
    IsSelfAdjoint (resolvent (G := G) h hh n) :=
  real_boundedMultiplier_selfAdjoint _ _ _

theorem resolvent_norm (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i) (n : ℕ) :
    ‖resolvent (G := G) h hh n‖ ≤ 1 := boundedMultiplier_norm _ _ _

include instDec in
theorem complement_strong_zero (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i) (x : Space G) :
    Tendsto (fun n => complement h hh n x) atTop (𝓝 0) := by
  apply boundedMultiplier_strong_zero
  intro i
  exact Complex.continuous_ofReal.continuousAt.tendsto.comp (complementWeight_tendsto_zero h i)

include instDec in
theorem resolvent_strong_one (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i) (x : Space G) :
    Tendsto (fun n => resolvent h hh n x) atTop (𝓝 x) := by
  have he : ∀ n, resolvent h hh n x = x - complement h hh n x := fun n => by
    have heq := resolvent_add_complement h hh n x
    exact eq_sub_iff_add_eq.mpr heq
  simp_rw [he]
  simpa using tendsto_const_nhds.sub (complement_strong_zero h hh x)

end StronglyRationalVOA.HilbertScale

namespace StronglyRationalVOA
theorem inner_tsum_left {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {g : ι → H} (hg : Summable g) (y : H) :
    inner ℂ (∑' i, g i) y = ∑' i, inner ℂ (g i) y :=
  ((innerSL ℂ).flip y).map_tsum hg

theorem inner_tsum_right {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {g : ι → H} (hg : Summable g) (x : H) :
    inner ℂ x (∑' i, g i) = ∑' i, inner ℂ x (g i) :=
  (innerSL ℂ x).map_tsum hg

theorem summable_inner_left {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {g : ι → H} (hg : Summable g) (y : H) :
    Summable (fun i => inner ℂ (g i) y) :=
  ((innerSL ℂ).flip y).summable hg

namespace RapidCoefficients

theorem int_mul {f : ℤ → ℂ} (hf : RapidCoefficients f) :
    RapidCoefficients (fun n => (n : ℂ)*f n) := by
  intro p
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _ (hf (p+1))
  intro n
  have hn : ‖(n : ℂ)‖ = |(n : ℝ)| := by
    rw [← Complex.ofReal_intCast,Complex.norm_real,Real.norm_eq_abs]
  rw [norm_mul,hn,pow_succ]
  have h := mul_nonneg (norm_nonneg (f n)) (pow_nonneg (by positivity : 0 ≤ 1+|(n : ℝ)|) p)
  nlinarith

end RapidCoefficients

namespace CFTTypeVOA
open UniformSpace
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  (A : CFTTypeVOA V)

 

theorem smearedMap_bound {a : V} {d k p : ℕ} (ha : A.PolynomialEnergyBound a)
    {f : ℤ → ℂ} (hf : RapidCoefficients f) {C : ℝ}
    (hb : ∀ n v, ‖A.physicalMode a d n v‖ ≤ C*(1+|(n : ℝ)|)^p*‖(A.energyShift^k) v‖)
    (v : V) :
    ‖A.smearedMap a d ha f hf v‖ ≤
      ((∑' n : ℤ, ‖f n‖*(1+|(n : ℝ)|)^p)*C)*‖(A.energyShift^k) v‖ := by
  rw [smearedMap_apply]
  apply (norm_tsum_le_tsum_norm (A.summable_norm_physicalSmear ha d hf v)).trans
  calc
    _ ≤ ∑' n : ℤ, (‖f n‖*(1+|(n : ℝ)|)^p)*(C*‖(A.energyShift^k) v‖) := by
      apply Summable.tsum_le_tsum _ (A.summable_norm_physicalSmear ha d hf v)
        ((hf p).mul_right _)
      intro n
      simp only [norm_smul,Completion.norm_coe]
      calc
        _ ≤ ‖f n‖*(C*(1+|(n : ℝ)|)^p*‖(A.energyShift^k) v‖) :=
          mul_le_mul_of_nonneg_left (hb n v) (norm_nonneg _)
        _ = _ := by ring
    _ = _ := by rw [tsum_mul_right]; ring

theorem energyShift_physical_commutator {a : V} {d : ℕ}
    (ha : a ∈ A.grade d) (n : ℤ) (v : V) :
    A.energyShift (A.physicalMode a d n v)-A.physicalMode a d n (A.energyShift v) =
      (-(n : ℂ)) • A.physicalMode a d n v := by
  have h := A.energy_mode_commutator ha (n+d-1) v
  simp only [Int.cast_sub,Int.cast_add,Int.cast_natCast,Int.cast_one] at h
  have he : (d : ℂ)-((n : ℂ)+d-1)-1 = -(n : ℂ) := by ring
  rw [he] at h
  simpa only [energyShift,LinearMap.add_apply,Module.End.one_apply,map_add,
    add_sub_add_left_eq_sub,physicalMode] using h

namespace UnitaryStructure
variable {A} (U : A.UnitaryStructure)

include U in
theorem energyShift_adjoint (x y : V) :
    inner ℂ (A.energyShift x) y = inner ℂ x (A.energyShift y) := by
  simp only [energyShift,LinearMap.add_apply,Module.End.one_apply,inner_add_left,
    inner_add_right,U.virasoro_adjoint,neg_zero]

 

theorem smearedMap_symmetric {a : V} {d : ℕ} (ha : a ∈ A.grade d)
    (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian d a) (he : A.PolynomialEnergyBound a)
    {f : ℤ → ℂ} (hf : RapidCoefficients f) (hreal : ∀ n, star (f n) = f (-n))
    (x y : V) :
    inner ℂ (A.smearedMap a d he f hf x) (y : Completion V) =
      inner ℂ (x : Completion V) (A.smearedMap a d he f hf y) := by
  rw [smearedMap_apply,smearedMap_apply,
    inner_tsum_left (A.summable_norm_physicalSmear he d hf x).of_norm,
    inner_tsum_right (A.summable_norm_physicalSmear he d hf y).of_norm]
  calc
    _ = ∑' n : ℤ, inner ℂ (x : Completion V)
        (f (-n) • (A.physicalMode a d (-n) y : Completion V)) := by
      apply tsum_congr
      intro n
      simp only [inner_smul_left,inner_smul_right,Completion.inner_coe,starRingEnd_apply,
        hreal,U.physicalMode_adjoint ha hq hh]
    _ = _ := (Equiv.neg ℤ).tsum_eq (fun n => inner ℂ (x : Completion V)
      (f n • (A.physicalMode a d n y : Completion V)))

 

theorem smearedMap_energy_commutator {a : V} {d : ℕ} (ha : a ∈ A.grade d)
    (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian d a) (he : A.PolynomialEnergyBound a)
    {f : ℤ → ℂ} (hf : RapidCoefficients f) (hreal : ∀ n, star (f n) = f (-n))
    (x y : V) :
    inner ℂ (A.smearedMap a d he f hf x) (A.energyShift y : Completion V)-
      inner ℂ (A.energyShift x : Completion V) (A.smearedMap a d he f hf y) =
    inner ℂ (A.smearedMap a d he (fun n => -(n : ℂ)*f n)
      (by simpa only [neg_mul,one_mul] using hf.int_mul.smul (-1)) x) (y : Completion V) := by
  have hf' : RapidCoefficients (fun n => -(n : ℂ)*f n) := by
    simpa only [neg_mul,one_mul] using hf.int_mul.smul (-1)
  rw [← U.smearedMap_symmetric ha hq hh he hf hreal (A.energyShift x) y]
  simp only [smearedMap_apply]
  rw [inner_tsum_left (A.summable_norm_physicalSmear he d hf x).of_norm,
      inner_tsum_left (A.summable_norm_physicalSmear he d hf (A.energyShift x)).of_norm,
      inner_tsum_left (A.summable_norm_physicalSmear he d hf' x).of_norm]
  rw [← (summable_inner_left (A.summable_norm_physicalSmear he d hf x).of_norm
    (A.energyShift y : Completion V)).tsum_sub
      (summable_inner_left (A.summable_norm_physicalSmear he d hf (A.energyShift x)).of_norm
        (y : Completion V))]
  apply tsum_congr
  intro n
  simp only [inner_smul_left,Completion.inner_coe]
  rw [← U.energyShift_adjoint,← mul_sub,← inner_sub_left,A.energyShift_physical_commutator ha,
    inner_smul_left]
  simp only [map_mul]
  ring

end UnitaryStructure
end CFTTypeVOA
end StronglyRationalVOA

namespace StronglyRationalVOA.HilbertScale
open Filter
open scoped Topology
variable {ι : Type*} {G : ι → Type u} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)] [DecidableEq ι] [∀ i, CompleteSpace (G i)]

omit [∀ i, CompleteSpace (G i)] in
theorem coreMultiplier_cancel (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i)
    (x : finiteCore (G := G)) :
    coreMultiplier (fun i => (h i : ℂ)) (coreMultiplier (fun i => (h i : ℂ)⁻¹) x) = x := by
  rw [coreMultiplier_mul]
  have hw : (fun i => (h i : ℂ) * (h i : ℂ)⁻¹) = fun _ => 1 := by
    funext i
    apply mul_inv_cancel₀
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one (hh i)))
  rw [hw,coreMultiplier_one]

omit [∀ i, CompleteSpace (G i)] in
theorem coreMultiplier_inv_cancel (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i)
    (x : finiteCore (G := G)) :
    coreMultiplier (fun i => (h i : ℂ)⁻¹) (coreMultiplier (fun i => (h i : ℂ)) x) = x := by
  rw [coreMultiplier_mul]
  have hw : (fun i => (h i : ℂ)⁻¹ * (h i : ℂ)) = fun _ => 1 := by
    funext i
    apply inv_mul_cancel₀
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one (hh i)))
  rw [hw,coreMultiplier_one]

 
def energyNormalized (h : ι → ℝ) (M : finiteCore (G := G) →ₗ[ℂ] Space G) :
    finiteCore (G := G) →ₗ[ℂ] Space G :=
  M.comp (coreMultiplier (fun i => (h i : ℂ)⁻¹))

 

def energyExtension (h : ι → ℝ) (M : finiteCore (G := G) →ₗ[ℂ] Space G) :
    Space G →L[ℂ] Space G :=
  (energyNormalized h M).extendOfNorm (finiteCore (G := G)).subtype

omit [∀ i, CompleteSpace (G i)] in
theorem energyNormalized_bound (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i)
    (M : finiteCore (G := G) →ₗ[ℂ] Space G) {C : ℝ}
    (hM : ∀ x, ‖M x‖ ≤ C * ‖coreDiagonal (fun i => (h i : ℂ)) x‖)
    (x : finiteCore (G := G)) : ‖energyNormalized h M x‖ ≤ C*‖(x : Space G)‖ := by
  have he : coreDiagonal (fun i => (h i : ℂ))
      (coreMultiplier (fun i => (h i : ℂ)⁻¹) x) = (x : Space G) :=
    congrArg Subtype.val (coreMultiplier_cancel h hh x)
  simpa only [energyNormalized,LinearMap.comp_apply,he] using
    hM (coreMultiplier (fun i => (h i : ℂ)⁻¹) x)

theorem energyExtension_core (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i)
    (M : finiteCore (G := G) →ₗ[ℂ] Space G) {C : ℝ}
    (hM : ∀ x, ‖M x‖ ≤ C * ‖coreDiagonal (fun i => (h i : ℂ)) x‖)
    (x : finiteCore (G := G)) :
    energyExtension h M x = M (coreMultiplier (fun i => (h i : ℂ)⁻¹) x) := by
  exact (energyNormalized h M).extendOfNorm_eq
    (e := (finiteCore (G := G)).subtype) (by simpa [DenseRange] using (finiteCore_dense (G := G)))
    ⟨C,energyNormalized_bound h hh M hM⟩ x

theorem energyExtension_weighted (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i)
    (M : finiteCore (G := G) →ₗ[ℂ] Space G) {C : ℝ}
    (hM : ∀ x, ‖M x‖ ≤ C * ‖coreDiagonal (fun i => (h i : ℂ)) x‖)
    (x : finiteCore (G := G)) :
    energyExtension h M (coreDiagonal (fun i => (h i : ℂ)) x) = M x := by
  change energyExtension h M ((coreMultiplier (fun i => (h i : ℂ)) x : finiteCore) : Space G) = _
  rw [energyExtension_core h hh M hM,coreMultiplier_inv_cancel h hh]

theorem energyExtension_norm (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i)
    (M : finiteCore (G := G) →ₗ[ℂ] Space G) {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ x, ‖M x‖ ≤ C * ‖coreDiagonal (fun i => (h i : ℂ)) x‖) :
    ‖energyExtension h M‖ ≤ C :=
  (energyNormalized h M).opNorm_extendOfNorm_le
    (e := (finiteCore (G := G)).subtype) (by simpa [DenseRange] using (finiteCore_dense (G := G)))
    hC (energyNormalized_bound h hh M hM)

theorem weighted_resolvent_core (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i) (n : ℕ)
    (x : finiteCore (G := G)) :
    coreDiagonal (fun i => (h i : ℂ))
      (coreMultiplier (fun i => (resolventWeight h n i : ℂ)) x) =
    ((n : ℂ)+1) • complement h hh n x := by
  apply lp.ext
  funext i
  simp only [coreDiagonal_apply,coreMultiplier_apply,lp.coeFn_smul,Pi.smul_apply,
    complement_apply,smul_smul]
  congr 1
  unfold resolventWeight complementWeight
  push_cast
  ring
end StronglyRationalVOA.HilbertScale

end

end OAI
