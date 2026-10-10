import Mathlib
import OAI.RepresentationTheory.VertexAlgebra.StressEvolution

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
namespace StronglyRationalVOA.HilbertScale
variable {G : ℕ → Type*} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)] [∀ i, CompleteSpace (G i)]
lemma energyCutoff_norm (n : ℕ) : ‖energyCutoff (G := G) n‖ ≤ 1 := boundedMultiplier_norm _ _ _

lemma energyCutoff_selfAdjoint (n : ℕ) : IsSelfAdjoint (energyCutoff (G := G) n) := by
  change (energyCutoff (G := G) n).adjoint=energyCutoff n
  unfold energyCutoff
  rw [boundedMultiplier_adjoint]
  ext x i
  simp only [boundedMultiplier_apply]
  split_ifs <;> simp

lemma energyCutoff_mul_self (n : ℕ) : energyCutoff (G := G) n*energyCutoff n=energyCutoff n := by
  ext x i
  change energyCutoff n (energyCutoff n x) i = energyCutoff n x i
  simp only [energyCutoff_apply]
  split_ifs <;> rfl

lemma energyCutoff_commute_multiplier (n : ℕ) (w : ℕ → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hw : ∀ i, ‖w i‖ ≤ C) :
    Commute (energyCutoff (G := G) n) (boundedMultiplier w hC hw) := by
  change _ * _ = _ * _
  ext x i
  change energyCutoff n (boundedMultiplier w hC hw x) i = boundedMultiplier w hC hw (energyCutoff n x) i
  simp only [energyCutoff_apply,boundedMultiplier_apply]
  split_ifs <;> simp

lemma energyCutoff_inverseEnergy (n r : ℕ) :
    Commute (energyCutoff (G := G) n)
      (inverseEnergy (fun i : ℕ => (1+(i:ℝ))^r) (fun i => one_le_pow₀ (le_add_of_nonneg_right (Nat.cast_nonneg i)))) :=
  energyCutoff_commute_multiplier _ _ _ _

def truncatedEnergyPower (n r : ℕ) : Space G →L[ℂ] Space G :=
  boundedMultiplier (fun i => if i ≤ n then (1+(i:ℂ))^r else 0)
    (show 0 ≤ (1+(n:ℝ))^r by positivity) (by
      intro i
      split_ifs with hi
      · rw [norm_pow]
        have hn : ‖(1:ℂ)+(i:ℂ)‖ = 1+(i:ℝ) := by
          rw [show (1:ℂ)+(i:ℂ) = ((1+(i:ℝ) : ℝ) : ℂ) by push_cast; rfl,
            Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
        rw [hn]
        exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.add_le_add_left hi 1) _
      · simpa using (show 0 ≤ (1+(n:ℝ))^r by positivity))

lemma truncatedEnergyPower_apply (n r : ℕ) (x : Space G) (i : ℕ) :
    truncatedEnergyPower n r x i = if i ≤ n then (1+(i:ℂ))^r • x i else 0 := by
  simp only [truncatedEnergyPower,boundedMultiplier_apply]
  split_ifs <;> simp

lemma inverseEnergy_truncated (n r : ℕ) :
    inverseEnergy (G := G) (fun i : ℕ => (1+(i:ℝ))^r) (fun i => one_le_pow₀ (le_add_of_nonneg_right (Nat.cast_nonneg i)))*
      truncatedEnergyPower n r = energyCutoff n := by
  ext x i
  change inverseEnergy (fun i : ℕ => (1+(i:ℝ))^r) (fun i => one_le_pow₀ (le_add_of_nonneg_right (Nat.cast_nonneg i))) (truncatedEnergyPower n r x) i = energyCutoff n x i
  rw [inverseEnergy_apply,truncatedEnergyPower_apply,energyCutoff_apply]
  split_ifs
  · rw [smul_smul]
    have he : (((1+(i:ℝ))^r : ℝ) : ℂ) = (1+(i:ℂ))^r := by push_cast; rfl
    rw [he,inv_mul_cancel₀,one_smul]
    apply pow_ne_zero
    have hp : (0:ℝ)<1+(i:ℝ) := by positivity
    exact_mod_cast ne_of_gt hp
  · rw [smul_zero]

lemma energyCutoff_tail_inverse (n : ℕ) :
    ‖(1-energyCutoff (G := G) n)*inverseEnergy (fun i : ℕ => 1+(i:ℝ)) (fun i => le_add_of_nonneg_right (Nat.cast_nonneg i))‖ ≤
      (1+(n:ℝ))⁻¹ := by
  let q (i : ℕ) : ℂ := if i ≤ n then 0 else (1+(i:ℂ))⁻¹
  have hb (i : ℕ) : ‖q i‖ ≤ (1+(n:ℝ))⁻¹ := by
    dsimp [q]
    split_ifs with hi
    · simpa using inv_nonneg.mpr (show (0:ℝ) ≤ 1+(n:ℝ) by positivity)
    · rw [norm_inv]
      have hn : ‖(1:ℂ)+(i:ℂ)‖ = 1+(i:ℝ) := by
        rw [show (1:ℂ)+(i:ℂ)=((1+(i:ℝ):ℝ):ℂ) by push_cast; rfl,
          Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
      rw [hn]
      apply inv_anti₀ (by positivity)
      exact_mod_cast Nat.add_le_add_left (Nat.le_of_lt (Nat.lt_of_not_ge hi)) 1
  have he : (1-energyCutoff (G := G) n)*inverseEnergy (fun i : ℕ => 1+(i:ℝ)) (fun i => le_add_of_nonneg_right (Nat.cast_nonneg i)) =
      boundedMultiplier q (by positivity) hb := by
    ext x i
    change inverseEnergy (fun i : ℕ => 1+(i:ℝ)) (fun i => le_add_of_nonneg_right (Nat.cast_nonneg i)) x i-energyCutoff n (inverseEnergy (fun i : ℕ => 1+(i:ℝ)) (fun i => le_add_of_nonneg_right (Nat.cast_nonneg i)) x) i = _
    simp only [energyCutoff_apply,inverseEnergy_apply,boundedMultiplier_apply,q]
    split_ifs <;> simp
  rw [he]
  exact boundedMultiplier_norm _ _ _
end StronglyRationalVOA.HilbertScale

namespace StronglyRationalVOA.SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma cutoff_selfAdjoint (T : H →ₗ.[ℂ] H) (hs : T.IsFormalAdjoint T)
    (P R : H →L[ℂ] H) (hP : IsSelfAdjoint P) (hg : ∀ x, (P x,R x) ∈ T.graph) :
    IsSelfAdjoint (P*R) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  change inner ℂ (P (R x)) y=inner ℂ x (P (R y))
  have hPa : P.adjoint=P := hP
  calc
    _ = inner ℂ (R x) (P y) := by rw [← P.adjoint_inner_right,hPa]
    _ = inner ℂ (P x) (R y) := formalAdjoint_graph_pairing hs (hg x) (hg y)
    _ = _ := by rw [← P.adjoint_inner_right,hPa]

omit [CompleteSpace H] in
lemma cutoff_normalized (T : H →ₗ.[ℂ] H)
    (P R S E : H →L[ℂ] H) (hg : ∀ x, (P x,R x) ∈ T.graph)
    (he : ∀ x, (S x,E x) ∈ T.graph) (hPS : Commute P S) :
    (P*R)*S=P*E*P := by
  ext x
  change P (R (S x))=P (E (P x))
  congr 1
  apply T.mem_graph_snd_inj (hg (S x)) (he (P x))
  exact congrArg (fun A : H →L[ℂ] H => A x) hPS.eq

 
lemma cutoff_commutator (T : H →ₗ.[ℂ] H) (hs : T.IsFormalAdjoint T)
    (P R S E F : H →L[ℂ] H) (hP : IsSelfAdjoint P) (hS : IsSelfAdjoint S)
    (hg : ∀ x, (P x,R x) ∈ T.graph) (he : ∀ x, (S x,E x) ∈ T.graph)
    (hPS : Commute P S) (hdef : E-E.adjoint = S*F) :
    S*(Complex.I • (P*R))-(Complex.I • (P*R))*S =
      (Complex.I • (P*F.adjoint*P))*S := by
  have hT := cutoff_selfAdjoint T hs P R hP hg
  have hn := cutoff_normalized T P R S E hg he hPS
  have ha : S*(P*R)=P*E.adjoint*P := by
    calc
      _ = star ((P*R)*S) := by rw [star_mul,show star S=S from hS,show star (P*R)=P*R from hT]
      _ = star (P*E*P) := congrArg star hn
      _ = _ := by rw [star_mul,star_mul,show star P=P from hP]; simp only [ContinuousLinearMap.star_eq_adjoint,mul_assoc]
  have hde : E.adjoint-E=F.adjoint*S := by
    have h := congrArg star hdef
    simpa only [star_sub,ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_adjoint,star_mul,show star S=S from hS] using h
  calc
    _ = Complex.I • (S*(P*R)-(P*R)*S) := by rw [mul_smul_comm,smul_mul_assoc,smul_sub]
    _ = Complex.I • (P*(E.adjoint-E)*P) := by rw [ha,hn]; congr 1; noncomm_ring
    _ = Complex.I • ((P*F.adjoint*P)*S) := by rw [hde]; congr 1; rw [mul_assoc,mul_assoc,← hPS.eq]; simp only [mul_assoc]
    _ = _ := by rw [smul_mul_assoc]

lemma cutoff_commutator_bound (P F : H →L[ℂ] H) (hP : ‖P‖ ≤ 1) :
    ‖Complex.I • (P*F.adjoint*P)‖ ≤ ‖F‖ := by
  rw [norm_smul,Complex.norm_I,one_mul]
  calc
    _ ≤ (‖P‖*‖F.adjoint‖)*‖P‖ := (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (1*‖F.adjoint‖)*1 := by gcongr
    _ = ‖F‖ := by rw [one_mul,mul_one,LinearIsometryEquiv.norm_map]

 

lemma cutoff_error (P S E A B : H →L[ℂ] H) (hP : ‖P‖ ≤ 1)
    (hleft : E=S*A) (hright : E=B*S) (hPS : Commute P S) {δ : ℝ}
    (htail : ‖(1-P)*S‖ ≤ δ) :
    ‖P*E*P-E‖ ≤ δ*(‖A‖+‖B‖) := by
  have hd : 0 ≤ δ := (norm_nonneg _).trans htail
  have hid : P*E*P-E = -(1-P)*E*P-E*(1-P) := by noncomm_ring
  have hrighttail : ‖S*(1-P)‖ ≤ δ := by
    have he : S*(1-P)=(1-P)*S := by rw [mul_sub,sub_mul,mul_one,one_mul,hPS.eq]
    rwa [he]
  rw [hid]
  calc
    _ ≤ ‖-(1-P)*E*P‖+‖E*(1-P)‖ := norm_sub_le _ _
    _ = ‖((1-P)*S)*A*P‖+‖B*(S*(1-P))‖ := by
      rw [neg_mul,neg_mul,norm_neg]
      congr 1
      · rw [hleft]; simp only [mul_assoc]
      · rw [hright]; simp only [mul_assoc]
    _ ≤ (‖(1-P)*S‖*‖A‖)*‖P‖+‖B‖*‖S*(1-P)‖ := add_le_add
      ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)))
      (norm_mul_le _ _)
    _ ≤ (δ*‖A‖)*1+‖B‖*δ := by gcongr
    _ = _ := by ring
end StronglyRationalVOA.SymmetricOperator

open UniformSpace Set
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
local instance : ∀ d : ℕ, FiniteDimensional ℂ (A.grade d) := A.grade_finite

lemma sobolevExtension_norm (r : ℕ) (M : V →ₗ[ℂ] Completion V) {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ v, ‖M v‖ ≤ C*‖(A.energyShift^r) v‖) : ‖U.sobolevExtension r M‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  rw [U.sobolevExtension_apply,LinearIsometryEquiv.norm_map]
  simpa only [LinearIsometryEquiv.norm_map] using
    (HilbertScale.energyExtension _ (U.spectralCoreMap M)).le_of_opNorm_le
      (HilbertScale.energyExtension_norm _ (fun i => one_le_pow₀ (le_add_of_nonneg_right (Nat.cast_nonneg i))) _ hC (U.spectralCoreMap_bound r M hM)) (U.energyCoordinates x)

def inverseCoreEnergy (r : ℕ) : V →ₗ[ℂ] V :=
  U.coreEnergyCoordinates.symm.toLinearMap.comp
    ((HilbertScale.coreMultiplier (fun d : ℕ => ((((1+(d:ℝ))^r : ℝ) : ℂ)⁻¹))).comp
      U.coreEnergyCoordinates.toLinearMap)

lemma inverseCoreEnergy_coe (r : ℕ) (v : V) :
    (U.inverseCoreEnergy r v : Completion V) = U.inverseSobolev r v := by
  apply U.energyCoordinates.injective
  rw [U.inverseSobolev_apply,U.energyCoordinates.apply_symm_apply]
  change (U.coreEnergyCoordinates (U.inverseCoreEnergy r v) : HilbertScale.Space (fun d => A.grade d)) = _
  simp only [inverseCoreEnergy,LinearMap.comp_apply,LinearEquiv.coe_toLinearMap,
    LinearEquiv.apply_symm_apply]
  exact (HilbertScale.inverseEnergy_core _ _ (U.coreEnergyCoordinates v)).symm

lemma energyShift_inverseCoreEnergy (r : ℕ) (v : V) :
    (A.energyShift^r) (U.inverseCoreEnergy r v)=v := by
  have h := U.inverseSobolev_graph r (v : Completion V)
  rw [← U.inverseCoreEnergy_coe] at h
  have hg : ((U.inverseCoreEnergy r v : V) : Completion V) =
    ((U.inverseCoreEnergy r v : V) : Completion V) := rfl
  have he : ((U.inverseCoreEnergy r v : Completion V),((A.energyShift^r) (U.inverseCoreEnergy r v) : Completion V)) ∈ (U.energyPower r).graph := (U.energyPower r).mem_graph_iff.mpr
    ⟨⟨_,U.coe_mem_energyOperator _ _⟩,rfl,U.energyPower_coe r (U.inverseCoreEnergy r v)⟩
  exact (Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V).injective
    ((U.energyPower r).mem_graph_snd_inj he h hg)

lemma sobolevExtension_coe (r : ℕ) (M : V →ₗ[ℂ] Completion V) {C : ℝ}
    (hM : ∀ v, ‖M v‖ ≤ C*‖(A.energyShift^r) v‖) (v : V) :
    U.sobolevExtension r M (v : Completion V)=M (U.inverseCoreEnergy r v) := by
  rw [U.sobolevExtension_apply,← U.coreEnergyCoordinates_coe,
    HilbertScale.energyExtension_core _ (fun i => one_le_pow₀ (le_add_of_nonneg_right (Nat.cast_nonneg i))) _ (U.spectralCoreMap_bound r M hM)]
  change U.energyCoordinates.symm (U.energyCoordinates (M (U.inverseCoreEnergy r v))) = _
  exact U.energyCoordinates.symm_apply_apply _

lemma sobolevExtension_sub_norm (r : ℕ) (M N : V →ₗ[ℂ] Completion V) {C D E : ℝ}
    (hM : ∀ v, ‖M v‖ ≤ C*‖(A.energyShift^r) v‖)
    (hN : ∀ v, ‖N v‖ ≤ D*‖(A.energyShift^r) v‖) (hE : 0 ≤ E)
    (hMN : ∀ v, ‖M v-N v‖ ≤ E*‖(A.energyShift^r) v‖) :
    ‖U.sobolevExtension r M-U.sobolevExtension r N‖ ≤ E := by
  apply ContinuousLinearMap.opNorm_le_bound _ hE
  intro x
  have hd : DenseRange (fun v : V => (v : Completion V)) := Completion.denseRange_coe
  apply hd.induction_on (p := fun x => ‖(U.sobolevExtension r M-U.sobolevExtension r N) x‖ ≤ E*‖x‖) x
    (isClosed_le (by fun_prop) (by fun_prop))
  intro v
  change ‖U.sobolevExtension r M (v : Completion V)-U.sobolevExtension r N (v : Completion V)‖ ≤ _
  rw [U.sobolevExtension_coe r M hM,U.sobolevExtension_coe r N hN,Completion.norm_coe]
  simpa only [U.energyShift_inverseCoreEnergy] using hMN (U.inverseCoreEnergy r v)

lemma inverseSobolev_mul (r s : ℕ) : U.inverseSobolev r*U.inverseSobolev s=U.inverseSobolev (r+s) := by
  ext x
  apply U.energyCoordinates.injective
  simp only [mul_apply_eq_comp,U.inverseSobolev_apply,U.energyCoordinates.apply_symm_apply]
  ext i
  simp only [HilbertScale.inverseEnergy_apply,smul_smul]
  congr 1
  push_cast
  rw [pow_add,mul_inv]

lemma sobolevExtension_lower (r s : ℕ) (M : V →ₗ[ℂ] Completion V) {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ v, ‖M v‖ ≤ C*‖(A.energyShift^r) v‖)
    (hc : (HilbertCore.operator M).IsClosable) :
    U.sobolevExtension (r+s) M=U.sobolevExtension r M*U.inverseSobolev s := by
  have hM' (v : V) : ‖M v‖ ≤ C*‖(A.energyShift^(r+s)) v‖ :=
    (hM v).trans (mul_le_mul_of_nonneg_left (U.energyShift_pow_norm_mono (Nat.le_add_right r s) v) hC)
  ext x
  have h1 := U.sobolevExtension_inverse_graph (r+s) M hM' hc x
  have h2 := U.sobolevExtension_inverse_graph r M hM hc (U.inverseSobolev s x)
  apply (HilbertCore.operator M).closure.mem_graph_snd_inj h1 h2
  exact congrArg (fun B : Completion V →L[ℂ] Completion V => B x) (U.inverseSobolev_mul r s).symm

end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
local instance : ∀ d : ℕ, FiniteDimensional ℂ (A.grade d) := A.grade_finite

def energyCutoff (n : ℕ) : Completion V →L[ℂ] Completion V :=
  U.energyCoordinates.symm.conjStarAlgEquiv (HilbertScale.energyCutoff n)

def truncatedEnergyPower (n r : ℕ) : Completion V →L[ℂ] Completion V :=
  U.energyCoordinates.symm.conjStarAlgEquiv (HilbertScale.truncatedEnergyPower n r)

lemma energyCutoff_norm (n : ℕ) : ‖U.energyCutoff n‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖U.energyCoordinates.symm (HilbertScale.energyCutoff n (U.energyCoordinates x))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  simpa only [LinearIsometryEquiv.norm_map] using
    (HilbertScale.energyCutoff (G := fun d => A.grade d) n).le_of_opNorm_le (HilbertScale.energyCutoff_norm n) (U.energyCoordinates x)

lemma energyCutoff_selfAdjoint (n : ℕ) : IsSelfAdjoint (U.energyCutoff n) := by
  change star (U.energyCutoff n)=U.energyCutoff n
  unfold energyCutoff
  exact (U.energyCoordinates.symm.conjStarAlgEquiv.map_star' _).symm.trans
    (congrArg U.energyCoordinates.symm.conjStarAlgEquiv (HilbertScale.energyCutoff_selfAdjoint n))

lemma energyCutoff_inverseSobolev (n r : ℕ) : Commute (U.energyCutoff n) (U.inverseSobolev r) := by
  exact (HilbertScale.energyCutoff_inverseEnergy n r).map U.energyCoordinates.symm.conjStarAlgEquiv

lemma inverseSobolev_truncated (n r : ℕ) :
    U.inverseSobolev r*U.truncatedEnergyPower n r=U.energyCutoff n := by
  change U.energyCoordinates.symm.conjStarAlgEquiv _ * U.energyCoordinates.symm.conjStarAlgEquiv _ = _
  rw [← map_mul,HilbertScale.inverseEnergy_truncated]
  rfl

lemma energyCutoff_tail_inverse (n : ℕ) :
    ‖(1-U.energyCutoff n)*U.inverseSobolev 1‖ ≤ (1+(n:ℝ))⁻¹ := by
  change ‖(1-U.energyCoordinates.symm.conjStarAlgEquiv _)*U.energyCoordinates.symm.conjStarAlgEquiv _‖ ≤ _
  rw [← map_one U.energyCoordinates.symm.conjStarAlgEquiv,← map_sub,← map_mul]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,LinearIsometryEquiv.norm_map]
  have h : ‖(1-HilbertScale.energyCutoff (G := fun d => A.grade d) n)*HilbertScale.inverseEnergy (fun d : ℕ => (1+(d:ℝ))^1) (fun d => one_le_pow₀ (le_add_of_nonneg_right (Nat.cast_nonneg d)))‖ ≤ (1+(n:ℝ))⁻¹ := by
    simpa only [pow_one] using (HilbertScale.energyCutoff_tail_inverse (G := fun d => A.grade d) n)
  simpa only [LinearIsometryEquiv.symm_symm,LinearIsometryEquiv.norm_map] using ContinuousLinearMap.le_of_opNorm_le _ h (U.energyCoordinates x)

lemma energyCutoff_graph (r : ℕ) (M : V →ₗ[ℂ] Completion V) {C : ℝ}
    (hM : ∀ v, ‖M v‖ ≤ C*‖(A.energyShift^r) v‖)
    (hc : (HilbertCore.operator M).IsClosable) (n : ℕ) (x : Completion V) :
    (U.energyCutoff n x,(U.sobolevExtension r M*U.truncatedEnergyPower n r) x) ∈
      (HilbertCore.operator M).closure.graph := by
  have h := U.sobolevExtension_inverse_graph r M hM hc (U.truncatedEnergyPower n r x)
  change ((U.inverseSobolev r*U.truncatedEnergyPower n r) x,_) ∈ _ at h
  rwa [U.inverseSobolev_truncated] at h
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Filter
open scoped Topology
namespace StronglyRationalVOA
namespace RapidCoefficients
variable {f g : ℤ → ℂ}
lemma neg (hf : RapidCoefficients f) : RapidCoefficients (fun n => -f n) := by
  simpa only [neg_one_mul] using hf.smul (-1)
lemma sub (hf : RapidCoefficients f) (hg : RapidCoefficients g) : RapidCoefficients (fun n => f n-g n) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg
end RapidCoefficients

def coefficientSeminorm (f : ℤ → ℂ) (r : ℕ) : ℝ := ∑' n : ℤ, ‖f n‖*(1+|(n:ℝ)|)^r
lemma coefficientSeminorm_nonneg (f : ℤ → ℂ) (r : ℕ) : 0 ≤ coefficientSeminorm f r :=
  tsum_nonneg (fun n => by positivity)

namespace CFTTypeVOA
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (A : CFTTypeVOA V)
lemma smearedMap_sub {a : V} (he : A.PolynomialEnergyBound a) (d : ℕ)
    {f g : ℤ → ℂ} (hf : RapidCoefficients f) (hg : RapidCoefficients g) :
    A.smearedMap a d he f hf-A.smearedMap a d he g hg =
      A.smearedMap a d he (fun n => f n-g n) (hf.sub hg) := by
  ext v
  simp only [LinearMap.sub_apply,smearedMap_apply,sub_smul]
  exact ((A.summable_norm_physicalSmear he d hf v).of_norm.tsum_sub
    (A.summable_norm_physicalSmear he d hg v).of_norm).symm

lemma smearedMap_difference_bound {a : V} (he : A.PolynomialEnergyBound a) {d p k : ℕ}
    {C : ℝ} (hb : ∀ n v, ‖A.physicalMode a d n v‖ ≤ C*(1+|(n:ℝ)|)^p*‖(A.energyShift^k) v‖)
    {f g : ℤ → ℂ} (hf : RapidCoefficients f) (hg : RapidCoefficients g) (v : V) :
    ‖A.smearedMap a d he f hf v-A.smearedMap a d he g hg v‖ ≤
      (coefficientSeminorm (fun n => f n-g n) p*C)*‖(A.energyShift^k) v‖ := by
  change ‖(A.smearedMap a d he f hf-A.smearedMap a d he g hg) v‖ ≤ _
  rw [A.smearedMap_sub he d hf hg]
  exact A.smearedMap_bound he (hf.sub hg) hb v
end CFTTypeVOA
end StronglyRationalVOA

open UniformSpace Filter
open scoped Topology
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

def stressCore (hc : A.toVertexAlgebra.C2Cofinite) {f : ℤ → ℂ} (hf : RapidCoefficients f) :
    V →ₗ[ℂ] Completion V := A.smearedMap A.conformalVector 2 (U.polynomialEnergyBounds hc _) f hf

def stressNormalized (hc : A.toVertexAlgebra.C2Cofinite) {f : ℤ → ℂ}
    (hf : RapidCoefficients f) (r : ℕ) : Completion V →L[ℂ] Completion V :=
  U.sobolevExtension r (U.stressCore hc hf)

lemma stressCore_bound (hc : A.toVertexAlgebra.C2Cofinite) {f : ℤ → ℂ}
    (hf : RapidCoefficients f) {r : ℕ} (hr : 1 ≤ r) (v : V) :
    ‖U.stressCore hc hf v‖ ≤
      (coefficientSeminorm f 2*(1+A.centralCharge.re))*‖(A.energyShift^r) v‖ := by
  have h := A.smearedMap_bound (U.polynomialEnergyBounds hc A.conformalVector) hf
    (k := 1) (by simpa only [pow_one] using U.stress_physical_bound) v
  exact h.trans (mul_le_mul_of_nonneg_left (U.energyShift_pow_norm_mono hr v)
    (mul_nonneg (coefficientSeminorm_nonneg _ _) (by linarith [U.centralCharge_nonneg])))

lemma stressNormalized_norm (hc : A.toVertexAlgebra.C2Cofinite) {f : ℤ → ℂ}
    (hf : RapidCoefficients f) {r : ℕ} (hr : 1 ≤ r) :
    ‖U.stressNormalized hc hf r‖ ≤ coefficientSeminorm f 2*(1+A.centralCharge.re) := by
  apply U.sobolevExtension_norm
    r (U.stressCore hc hf) (mul_nonneg (coefficientSeminorm_nonneg _ _) (by linarith [U.centralCharge_nonneg]))
  exact U.stressCore_bound hc hf hr

lemma stressNormalized_graph (hc : A.toVertexAlgebra.C2Cofinite) {f : ℤ → ℂ}
    (hf : RapidCoefficients f) {r : ℕ} (hr : 1 ≤ r) (x : Completion V) :
    (U.inverseSobolev r x,U.stressNormalized hc hf r x) ∈
      (U.closedSmearedOperator hc A.conformalVector 2 f hf).graph := by
  exact U.sobolevExtension_inverse_graph r _ (U.stressCore_bound hc hf hr)
    (U.smearedCore_closable hc A.conformal_mem hf) x

lemma stressNormalized_difference (hc : A.toVertexAlgebra.C2Cofinite) {f g : ℤ → ℂ}
    (hf : RapidCoefficients f) (hg : RapidCoefficients g) {r : ℕ} (hr : 1 ≤ r) :
    ‖U.stressNormalized hc hf r-U.stressNormalized hc hg r‖ ≤
      coefficientSeminorm (fun n => f n-g n) 2*(1+A.centralCharge.re) := by
  apply U.sobolevExtension_sub_norm r _ _ (U.stressCore_bound hc hf hr) (U.stressCore_bound hc hg hr)
    (mul_nonneg (coefficientSeminorm_nonneg _ _) (by linarith [U.centralCharge_nonneg]))
  intro v
  have h := A.smearedMap_difference_bound (U.polynomialEnergyBounds hc A.conformalVector)
    (k := 1) (by simpa only [pow_one] using U.stress_physical_bound) hf hg v
  exact h.trans (mul_le_mul_of_nonneg_left (U.energyShift_pow_norm_mono hr v)
    (mul_nonneg (coefficientSeminorm_nonneg _ _) (by linarith [U.centralCharge_nonneg])))

lemma stressNormalized_continuous (hc : A.toVertexAlgebra.C2Cofinite)
    {f : ℝ → ℤ → ℂ} (hf : ∀ t, RapidCoefficients (f t))
    (hl : ∀ t, Tendsto (fun s => coefficientSeminorm (fun n => f s n-f t n) 2) (𝓝 t) (𝓝 0))
    {r : ℕ} (hr : 1 ≤ r) : Continuous (fun t => U.stressNormalized hc (hf t) r) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  rw [ContinuousAt,tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero (fun _ => norm_nonneg _) (fun s => U.stressNormalized_difference hc (hf s) (hf t) hr)
  simpa only [zero_mul] using (hl t).mul_const (1+A.centralCharge.re)

lemma stressNormalized_two_factor (hc : A.toVertexAlgebra.C2Cofinite) {f : ℤ → ℂ}
    (hf : RapidCoefficients f) :
    ∃ B : Completion V →L[ℂ] Completion V,
      U.stressNormalized hc hf 2=U.inverseSobolev 1*B ∧
      ‖B‖ ≤ coefficientSeminorm f 3*(1+A.centralCharge.re) ∧
      U.stressNormalized hc hf 2=U.stressNormalized hc hf 1*U.inverseSobolev 1 := by
  let N := U.weightedSmearedMap A.conformal_mem (U.polynomialEnergyBounds hc A.conformalVector) hf 1
  have hN (v : V) : ‖N v‖ ≤ (coefficientSeminorm f 3*(1+A.centralCharge.re))*‖(A.energyShift^2) v‖ := by
    exact U.smearedMap_sobolev_bound A.conformal_mem (U.polynomialEnergyBounds hc _)
      (k := 1) (by linarith [U.centralCharge_nonneg])
      (by simpa only [pow_one] using U.stress_physical_bound) hf 1 v
  refine ⟨U.sobolevExtension 2 N,?_,U.sobolevExtension_norm 2 N
      (mul_nonneg (coefficientSeminorm_nonneg _ _) (by linarith [U.centralCharge_nonneg])) hN,?_⟩
  · ext x
    have h := U.sobolevExtension_graph 2 (U.stressCore hc hf) N
      (U.stressCore_bound hc hf (by norm_num : 1 ≤ 2)) hN (U.energyPower 1)
      (U.energyOperator_closed _) (U.smearedMap_energyGraph A.conformal_mem (U.polynomialEnergyBounds hc _) hf 1) x
    exact (U.inverseSobolev_on_graph 1 h).symm
  · exact U.sobolevExtension_lower 1 1 (U.stressCore hc hf)
      (mul_nonneg (coefficientSeminorm_nonneg _ _) (by linarith [U.centralCharge_nonneg]))
      (U.stressCore_bound hc hf le_rfl) (U.smearedCore_closable hc A.conformal_mem hf)

lemma stressNormalized_defect (hc : A.toVertexAlgebra.C2Cofinite) {f : ℤ → ℂ}
    (hf : RapidCoefficients f) (hreal : ∀ n, star (f n)=f (-n)) {r : ℕ} (hr : 1 ≤ r) :
    ∃ F : Completion V →L[ℂ] Completion V,
      U.stressNormalized hc hf r-(U.stressNormalized hc hf r).adjoint=U.inverseSobolev r*F ∧
      ‖F‖ ≤ coefficientSeminorm f (2+r)*((1+A.centralCharge.re)*r) := by
  let K := U.smearedPowerCommutator A.conformal_mem (U.polynomialEnergyBounds hc A.conformalVector) hf r
  have hC : 0 ≤ 1+A.centralCharge.re := by linarith [U.centralCharge_nonneg]
  have hK (v : V) : ‖K v‖ ≤ (coefficientSeminorm f (2+r)*((1+A.centralCharge.re)*r))*‖(A.energyShift^r) v‖ :=
    U.smearedPowerCommutator_bound A.conformal_mem (U.polynomialEnergyBounds hc _) hC U.stress_physical_bound hf r v
  refine ⟨U.sobolevExtension r K,?_,U.sobolevExtension_norm r K
    (mul_nonneg (coefficientSeminorm_nonneg _ _) (mul_nonneg hC (Nat.cast_nonneg r))) hK⟩
  exact U.sobolevExtension_defect r _ K (U.stressCore_bound hc hf hr) hK
    (U.smearedPowerCommutator_pairing A.conformal_mem A.conformal_quasiPrimary U.stress_hermitian
      (U.polynomialEnergyBounds hc _) hf hreal r)
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Filter
open scoped Topology
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
local instance : ∀ d : ℕ, FiniteDimensional ℂ (A.grade d) := A.grade_finite

lemma truncatedEnergyPower_norm (n r : ℕ) : ‖U.truncatedEnergyPower n r‖ ≤ (1+(n:ℝ))^r := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  change ‖U.energyCoordinates.symm (HilbertScale.truncatedEnergyPower n r (U.energyCoordinates x))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  have h : ‖HilbertScale.truncatedEnergyPower (G := fun d => A.grade d) n r‖ ≤ (1+(n:ℝ))^r :=
    HilbertScale.boundedMultiplier_norm _ _ _
  simpa only [LinearIsometryEquiv.norm_map] using ContinuousLinearMap.le_of_opNorm_le _ h (U.energyCoordinates x)

 

def stressCutoff (hc : A.toVertexAlgebra.C2Cofinite) (n : ℕ) {f : ℤ → ℂ}
    (hf : RapidCoefficients f) : Completion V →L[ℂ] Completion V :=
  Complex.I • (U.energyCutoff n*(U.stressNormalized hc hf 1*U.truncatedEnergyPower n 1))

lemma stressCutoff_norm (hc : A.toVertexAlgebra.C2Cofinite) (n : ℕ) {f : ℤ → ℂ}
    (hf : RapidCoefficients f) :
    ‖U.stressCutoff hc n hf‖ ≤ (coefficientSeminorm f 2*(1+A.centralCharge.re))*(1+(n:ℝ)) := by
  rw [stressCutoff,norm_smul,Complex.norm_I,one_mul]
  calc
    _ ≤ ‖U.energyCutoff n‖*(‖U.stressNormalized hc hf 1‖*‖U.truncatedEnergyPower n 1‖) :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ 1*((coefficientSeminorm f 2*(1+A.centralCharge.re))*(1+(n:ℝ))^1) := by
      gcongr
      · exact U.energyCutoff_norm n
      · exact mul_nonneg (coefficientSeminorm_nonneg _ _) (by linarith [U.centralCharge_nonneg])
      · exact U.stressNormalized_norm hc hf le_rfl
      · exact U.truncatedEnergyPower_norm n 1
    _ = _ := by rw [pow_one,one_mul]

lemma stressCore_formalAdjoint (hc : A.toVertexAlgebra.C2Cofinite) {f : ℤ → ℂ}
    (hf : RapidCoefficients f) (hr : ∀ n, star (f n)=f (-n)) :
    (U.closedSmearedOperator hc A.conformalVector 2 f hf).IsFormalAdjoint
      (U.closedSmearedOperator hc A.conformalVector 2 f hf) := by
  exact SymmetricOperator.formalAdjoint_closure (U.smearedCore_closable hc A.conformal_mem hf)
    (U.smearedCore_closable hc A.conformal_mem hf)
    (HilbertCore.formalAdjoint (U.smearedMap_symmetric A.conformal_mem A.conformal_quasiPrimary
      U.stress_hermitian (U.polynomialEnergyBounds hc _) hf hr))

lemma stressCutoff_skew (hc : A.toVertexAlgebra.C2Cofinite) (n : ℕ) {f : ℤ → ℂ}
    (hf : RapidCoefficients f) (hr : ∀ m, star (f m)=f (-m)) :
    star (U.stressCutoff hc n hf) = -U.stressCutoff hc n hf := by
  have hs := SymmetricOperator.cutoff_selfAdjoint
    (U.closedSmearedOperator hc A.conformalVector 2 f hf) (U.stressCore_formalAdjoint hc hf hr)
    (U.energyCutoff n) (U.stressNormalized hc hf 1*U.truncatedEnergyPower n 1)
    (U.energyCutoff_selfAdjoint n)
    (U.energyCutoff_graph 1 (U.stressCore hc hf) (U.stressCore_bound hc hf le_rfl)
      (U.smearedCore_closable hc A.conformal_mem hf) n)
  rw [stressCutoff,star_smul,show star (_ : Completion V →L[ℂ] Completion V)=_ from hs]
  simp only [Complex.star_def,Complex.conj_I,neg_smul]
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

end

end OAI
