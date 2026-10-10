import Mathlib
import OAI.RepresentationTheory.VertexAlgebra.InverseEnergySelf

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
namespace StronglyRationalVOA.BoundedFlow
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance boundedFlowRationalNormedAlgebra : NormedAlgebra ℚ (H →L[ℂ] H) :=
  .restrictScalars ℚ ℂ (H →L[ℂ] H)

def flow (K : H →L[ℂ] H) (t : ℝ) : H →L[ℂ] H := NormedSpace.exp (t • K)

lemma flow_unitary {K : H →L[ℂ] H} (hK : K ∈ skewAdjoint (H →L[ℂ] H)) (t : ℝ) :
    flow K t ∈ unitary (H →L[ℂ] H) := by
  apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
  change star (t • K) = -(t • K)
  rw [star_smul,star_trivial,skewAdjoint.mem_iff.mp hK,smul_neg]

lemma flow_norm {K : H →L[ℂ] H} (hK : K ∈ skewAdjoint (H →L[ℂ] H)) (t : ℝ) (x : H) :
    ‖flow K t x‖ = ‖x‖ := ContinuousLinearMap.norm_map_of_mem_unitary (flow_unitary hK t) x

lemma flow_derivative (K : H →L[ℂ] H) (t : ℝ) (x : H) :
    HasDerivAt (fun s : ℝ => flow K s x) (flow K t (K x)) t := by
  exact ((ContinuousLinearMap.apply ℂ H x).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_exp_smul_const K t)

lemma flow_zero (K : H →L[ℂ] H) : flow K 0 = 1 := by simp [flow]

lemma flow_add (K : H →L[ℂ] H) (s t : ℝ) : flow K (s+t) = flow K s*flow K t := by
  simp only [flow,add_smul]
  exact NormedSpace.exp_add_of_commute (((Commute.refl K).smul_left s).smul_right t)

lemma flow_generator_commute (K : H →L[ℂ] H) (t : ℝ) : Commute K (flow K t) :=
  ((Commute.refl K).smul_right t).exp_right

lemma flow_commute {K L : H →L[ℂ] H} (hKL : Commute K L) (s t : ℝ) :
    Commute (flow K s) (flow L t) :=
  (((hKL.smul_left s).smul_right t).exp_right.symm.exp_right).symm

lemma flow_time_bound {K : H →L[ℂ] H} (hK : K ∈ skewAdjoint (H →L[ℂ] H))
    (s t : ℝ) (x : H) : ‖flow K t x-flow K s x‖ ≤ ‖K x‖*|t-s| := by
  have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun t : ℝ => flow K t x) (f' := fun t : ℝ => flow K t (K x))
    (s := Set.univ) (x := s) (y := t)
    (fun t _ => (flow_derivative K t x).hasDerivWithinAt)
    (fun t _ => (flow_norm hK t (K x)).le) convex_univ (Set.mem_univ _) (Set.mem_univ _)
  simpa only [Real.norm_eq_abs] using hb

lemma flow_initial_bound {K : H →L[ℂ] H} (hK : K ∈ skewAdjoint (H →L[ℂ] H))
    (t : ℝ) (x : H) : ‖flow K t x-x‖ ≤ |t| *‖K x‖ := by
  simpa only [flow_zero,one_apply_eq_self,sub_zero,mul_comm] using flow_time_bound hK 0 t x

lemma flow_difference {K L : H →L[ℂ] H} (hK : K ∈ skewAdjoint (H →L[ℂ] H))
    (hL : L ∈ skewAdjoint (H →L[ℂ] H)) (hKL : Commute K L) (t : ℝ) (x : H) :
    ‖flow K t x-flow L t x‖ ≤ |t| *‖(K-L) x‖ := by
  have hD : K-L ∈ skewAdjoint (H →L[ℂ] H) := by
    change star (K-L) = -(K-L)
    rw [star_sub,skewAdjoint.mem_iff.mp hK,skewAdjoint.mem_iff.mp hL]
    abel
  have hfactor : flow K t = flow L t*flow (K-L) t := by
    rw [flow,flow,flow,← NormedSpace.exp_add_of_commute]
    · congr 1
      module
    · exact ((hKL.symm.sub_right (Commute.refl L)).smul_left t).smul_right t
  rw [hfactor]
  change ‖flow L t (flow (K-L) t x)-flow L t x‖ ≤ _
  rw [← map_sub,flow_norm hL]
  exact flow_initial_bound hD t x

end StronglyRationalVOA.BoundedFlow

open scoped Topology
open Filter
namespace StronglyRationalVOA.StrongLimit
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
lemma equicontinuous_of_norm_bound {ι : Type*} (F : ι → H →L[ℂ] H) {C : ℝ}
    (hF : ∀ n, ‖F n‖ ≤ C) : Equicontinuous (fun n => (F n : H → H)) := by
  apply Metric.equicontinuous_of_continuity_modulus (fun t : ℝ => C*t)
    (by
      convert (continuous_const.mul continuous_id : Continuous (fun t : ℝ => C*t)).tendsto
        (0 : ℝ) using 1
      simp)
  intro x y n
  rw [dist_eq_norm,← map_sub,dist_eq_norm]
  exact (F n).le_of_opNorm_le (hF n) (x-y)

lemma exists_of_dense_core (D : Submodule ℂ H) (hD : Dense (D : Set H))
    (F : ℕ → H →L[ℂ] H) {C : ℝ} (hF : ∀ n, ‖F n‖ ≤ C)
    (hcore : ∀ x : D, CauchySeq (fun n => F n x)) :
    ∃ L : H →L[ℂ] H, ∀ x : H, Tendsto (fun n => F n x) atTop (𝓝 (L x)) := by
  choose f hf using fun x : D => cauchySeq_tendsto_of_complete (hcore x)
  let B : D →ₗ[ℂ] H :=
    { toFun := f
      map_add' := by
        intro x y
        apply tendsto_nhds_unique (hf (x+y))
        simpa only [Submodule.coe_add,map_add] using (hf x).add (hf y)
      map_smul' := by
        intro c x
        apply tendsto_nhds_unique (hf (c • x))
        simpa only [Submodule.coe_smul,map_smul,RingHom.id_apply] using (hf x).const_smul c }
  have hb : ∀ x : D, ‖B x‖ ≤ C*‖x‖ := by
    intro x
    apply le_of_tendsto (hf x).norm
    exact Filter.Eventually.of_forall fun n => (F n).le_of_opNorm_le (hF n) x
  let K := B.mkContinuous C hb
  let L := K.extend D.subtypeL
  have hd : DenseRange D.subtypeL := by
    change Dense (Set.range (D.subtypeL : D → H))
    have hr : Set.range (D.subtypeL : D → H) = (D : Set H) := by
      ext x
      exact ⟨by rintro ⟨y,rfl⟩; exact y.property,fun hx => ⟨⟨x,hx⟩,rfl⟩⟩
    rw [hr]
    exact hD
  have he : IsUniformInducing D.subtypeL := D.subtypeₗᵢ.isometry.isUniformInducing
  have hc := (equicontinuous_of_norm_bound F hF).isClosed_setOfPred_tendsto (l := atTop) L.continuous
  refine ⟨L,fun x => ?_⟩
  apply (closure_minimal (s := (D : Set H)) (t := {x | Tendsto (fun n => F n x) atTop (𝓝 (L x))}) ?_ hc) (hD x)
  intro x hx
  let v : D := ⟨x,hx⟩
  change Tendsto (fun n => F n (v : H)) atTop (𝓝 (K.extend D.subtypeL (D.subtypeL v)))
  rw [ContinuousLinearMap.extend_eq K hd he]
  exact hf v

omit [CompleteSpace H] in
lemma mul_tendsto (F G : ℕ → H →L[ℂ] H) (A B : H →L[ℂ] H) {C : ℝ}
    (hF : ∀ n, ‖F n‖ ≤ C)
    (hf : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (A x)))
    (hg : ∀ x, Tendsto (fun n => G n x) atTop (𝓝 (B x))) (x : H) :
    Tendsto (fun n => F n (G n x)) atTop (𝓝 (A (B x))) := by
  have hz : Tendsto (fun n => F n (G n x-B x)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (a := fun n => C*‖G n x-B x‖)
    · exact fun n => (F n).le_of_opNorm_le (hF n) _
    · simpa only [sub_self,norm_zero,mul_zero] using
        (tendsto_const_nhds.mul ((hg x).sub_const (B x)).norm)
  have h := hz.add (hf (B x))
  simpa only [map_sub,sub_add_cancel,zero_add] using h

end StronglyRationalVOA.StrongLimit

open scoped Topology
namespace StronglyRationalVOA.SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma resolvent_on_graph (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (z : ℂ) (hz : 1 ≤ |z.im|) {x y : H} (hxy : (x,y) ∈ T.graph) :
    resolvent T hs z hz y = x+z • resolvent T hs z hz x := by
  obtain ⟨v,hv,hTv⟩ := T.mem_graph_iff.mp hxy
  dsimp only [Prod.fst,Prod.snd] at hv hTv
  have he := resolvent_shift T hs z hz v
  rw [hv,hTv,map_sub,map_smul] at he
  exact (sub_eq_iff_eq_add.mp he)

lemma resolvent_commute (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (z w : ℂ) (hz : 1 ≤ |z.im|) (hw : 1 ≤ |w.im|) :
    Commute (resolvent T hs z hz) (resolvent T hs w hw) := by
  apply ContinuousLinearMap.ext
  intro x
  let R := resolvent T hs z hz
  let S := resolvent T hs w hw
  have hg := resolvent_graph T hs z hz (S x)
  have he := resolvent_on_graph T hs z hz (resolvent_graph T hs w hw x)
  have hg' : (R (S x),R x+w • R (S x)) ∈ T.graph := by
    have hoe : S x+z • R (S x) = R x+w • R (S x) := by
      simpa only [map_add,map_smul] using he.symm
    simpa only [R,hoe] using hg
  have hn := resolvent_on_graph T hs w hw hg'
  simp only [map_add,map_smul] at hn
  change R (S x) = S (R x)
  exact (add_right_cancel hn).symm

lemma imaginary_modulus (r : ℝ) : |((r : ℂ)*Complex.I).im| = |r| := by simp

 
def regularizer (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (r : ℝ) (hr : 1 ≤ r) : H →L[ℂ] H :=
  (-(r : ℂ)*Complex.I/2) •
    (resolvent T hs ((r : ℂ)*Complex.I) (by simpa [abs_of_nonneg (by linarith : 0 ≤ r)] using hr) -
     resolvent T hs (-((r : ℂ)*Complex.I)) (by simpa [abs_of_nonneg (by linarith : 0 ≤ r)] using hr))

def boundedGenerator (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (r : ℝ) (hr : 1 ≤ r) : H →L[ℂ] H :=
  ((r : ℂ)^2/2) •
    (resolvent T hs ((r : ℂ)*Complex.I) (by simpa [abs_of_nonneg (by linarith : 0 ≤ r)] using hr) +
     resolvent T hs (-((r : ℂ)*Complex.I)) (by simpa [abs_of_nonneg (by linarith : 0 ≤ r)] using hr))

lemma regularizer_graph (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (r : ℝ) (hr : 1 ≤ r) (x : H) :
    (regularizer T hs r hr x,boundedGenerator T hs r hr x) ∈ T.graph := by
  let z : ℂ := (r : ℂ)*Complex.I
  have hz : 1 ≤ |z.im| := by simpa [z,abs_of_nonneg (by linarith : 0 ≤ r)] using hr
  have hz' : 1 ≤ |(-z).im| := by simpa using hz
  have hg := T.graph.smul_mem (-(r : ℂ)*Complex.I/2)
    (T.graph.sub_mem (resolvent_graph T hs z hz x) (resolvent_graph T hs (-z) hz' x))
  convert hg using 1
  apply Prod.ext
  · simp [regularizer,z]
  · change ((r : ℂ)^2/2) • (resolvent T hs z hz x+resolvent T hs (-z) hz' x) =
      (-(r : ℂ)*Complex.I/2) • ((x+z • resolvent T hs z hz x)-
        (x+(-z) • resolvent T hs (-z) hz' x))
    simp only [add_sub_add_left_eq_sub,smul_sub,smul_add,smul_smul,neg_smul,z]
    have h1 : (-(r : ℂ)*Complex.I/2)*((r : ℂ)*Complex.I) = (r : ℂ)^2/2 := by
      calc _ = -(r : ℂ)^2*Complex.I^2/2 := by ring
           _ = _ := by rw [Complex.I_sq]; ring
    rw [h1]
    match_scalars
    all_goals first | ring1 | (ring_nf; simp only [Complex.I_sq]; ring)

lemma boundedGenerator_selfAdjoint (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (r : ℝ) (hr : 1 ≤ r) : IsSelfAdjoint (boundedGenerator T hs r hr) := by
  change star (boundedGenerator T hs r hr) = _
  rw [boundedGenerator,star_smul,star_add]
  change star ((r : ℂ)^2/2) •
    ((resolvent T hs ((r : ℂ)*Complex.I) _).adjoint+
     (resolvent T hs (-((r : ℂ)*Complex.I)) _).adjoint) = _
  rw [resolvent_adjoint,resolvent_adjoint]
  simp only [map_div₀,map_pow,Complex.star_def,Complex.conj_ofReal,map_ofNat,
    map_mul,Complex.conj_I,map_neg,mul_neg,neg_neg]
  exact congrArg (fun X : H →L[ℂ] H => ((r : ℂ)^2/2) • X) (add_comm _ _)

lemma regularizer_norm_le (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (r : ℝ) (hr : 1 ≤ r) : ‖regularizer T hs r hr‖ ≤ 1 := by
  have hr0 : 0 < r := by linarith
  calc
    _ ≤ ‖-(r : ℂ)*Complex.I/2‖ *
        (‖resolvent T hs ((r : ℂ)*Complex.I) _‖ + ‖resolvent T hs (-((r : ℂ)*Complex.I)) _‖) := by
      dsimp only [regularizer]
      rw [norm_smul]
      gcongr
      exact norm_sub_le _ _
    _ ≤ ‖-(r : ℂ)*Complex.I/2‖ * (r⁻¹+r⁻¹) := by
      gcongr
      · simpa [abs_of_pos hr0] using resolvent_norm_le T hs ((r : ℂ)*Complex.I) (by simpa [abs_of_pos hr0] using hr)
      · simpa [abs_of_pos hr0] using resolvent_norm_le T hs (-((r : ℂ)*Complex.I)) (by simpa [abs_of_pos hr0] using hr)
    _ = 1 := by simp [Complex.norm_real,abs_of_pos hr0]; field_simp; norm_num

lemma boundedGenerator_commute (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (r s : ℝ) (hr : 1 ≤ r) (hs' : 1 ≤ s) :
    Commute (boundedGenerator T hs r hr) (boundedGenerator T hs s hs') := by
  unfold boundedGenerator
  apply Commute.smul_left
  apply Commute.smul_right
  apply Commute.add_left
  · apply Commute.add_right <;> exact resolvent_commute T hs _ _ _ _
  · apply Commute.add_right <;> exact resolvent_commute T hs _ _ _ _

lemma regularizer_on_graph (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (r : ℝ) (hr : 1 ≤ r) {x y : H} (hxy : (x,y) ∈ T.graph) :
    boundedGenerator T hs r hr x = regularizer T hs r hr y := by
  let z : ℂ := (r : ℂ)*Complex.I
  have hz : 1 ≤ |z.im| := by simpa [z,abs_of_nonneg (by linarith : 0 ≤ r)] using hr
  have hz' : 1 ≤ |(-z).im| := by simpa using hz
  change ((r : ℂ)^2/2) • (resolvent T hs z hz x+resolvent T hs (-z) hz' x) =
      (-(r : ℂ)*Complex.I/2) • (resolvent T hs z hz y-resolvent T hs (-z) hz' y)
  rw [resolvent_on_graph T hs z hz hxy,resolvent_on_graph T hs (-z) hz' hxy]
  simp only [add_sub_add_left_eq_sub,smul_sub,smul_add,smul_smul,neg_smul,z]
  have h1 : (-(r : ℂ)*Complex.I/2)*((r : ℂ)*Complex.I) = (r : ℂ)^2/2 := by
    calc _ = -(r : ℂ)^2*Complex.I^2/2 := by ring
         _ = _ := by rw [Complex.I_sq]; ring
  rw [h1]
  match_scalars
  all_goals first | ring1 | (ring_nf; simp only [Complex.I_sq]; ring)

lemma regularizer_error (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (r : ℝ) (hr : 1 ≤ r) {x y : H} (hxy : (x,y) ∈ T.graph) :
    ‖regularizer T hs r hr x-x‖ ≤ r⁻¹*‖y‖ := by
  let z : ℂ := (r : ℂ)*Complex.I
  have hr0 : 0 < r := by linarith
  have hz : 1 ≤ |z.im| := by simpa [z,abs_of_pos hr0] using hr
  have hz' : 1 ≤ |(-z).im| := by simpa using hz
  have he : regularizer T hs r hr x-x =
      (-1/2 : ℂ) • (resolvent T hs z hz y+resolvent T hs (-z) hz' y) := by
    rw [resolvent_on_graph T hs z hz hxy,resolvent_on_graph T hs (-z) hz' hxy]
    simp only [regularizer,smul_apply,sub_apply,z]
    module
  rw [he,norm_smul]
  calc
    _ ≤ ‖(-1/2 : ℂ)‖ * (‖resolvent T hs z hz y‖+‖resolvent T hs (-z) hz' y‖) := by
      gcongr; exact norm_add_le _ _
    _ ≤ ‖(-1/2 : ℂ)‖ * ((‖resolvent T hs z hz‖+‖resolvent T hs (-z) hz'‖)*‖y‖) := by
      rw [add_mul]; gcongr <;> exact ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖(-1/2 : ℂ)‖ * ((r⁻¹+r⁻¹)*‖y‖) := by
      gcongr
      · simpa [z,abs_of_pos hr0] using resolvent_norm_le T hs z hz
      · simpa [z,abs_of_pos hr0] using resolvent_norm_le T hs (-z) hz'
    _ = _ := by norm_num; ring

end StronglyRationalVOA.SymmetricOperator

open scoped Topology
open Filter
namespace StronglyRationalVOA.SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

abbrev sampleRadius (n : ℕ) : ℝ := (n : ℝ)+1
lemma sampleRadius_ge (n : ℕ) : 1 ≤ sampleRadius n := by
  dsimp [sampleRadius]
  linarith [Nat.cast_nonneg (α := ℝ) n]

lemma regularizer_strong (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (x : H) :
    Tendsto (fun n : ℕ => regularizer T hs (sampleRadius n) (sampleRadius_ge n) x) atTop (𝓝 x) := by
  have he : Equicontinuous (fun n : ℕ => (regularizer T hs (sampleRadius n) (sampleRadius_ge n) : H → H)) :=
    StrongLimit.equicontinuous_of_norm_bound _ (fun n => regularizer_norm_le T hs _ _)
  have hc := he.isClosed_setOfPred_tendsto (l := atTop) (f := id) continuous_id
  apply (closure_minimal (s := (T.domain : Set H)) (t := {x | Tendsto
    (fun n : ℕ => regularizer T hs (sampleRadius n) (sampleRadius_ge n) x) atTop (𝓝 x)}) ?_ hc) (hs.dense_domain x)
  intro x hx
  let v : T.domain := ⟨x,hx⟩
  change Tendsto _ _ _
  rw [← tendsto_sub_nhds_zero_iff]
  apply squeeze_zero_norm (a := fun n : ℕ => (sampleRadius n)⁻¹*‖T v‖)
  · intro n
    exact regularizer_error T hs _ _ (T.mem_graph_iff.mpr ⟨v,rfl,rfl⟩)
  · have ht : Tendsto (fun n : ℕ => sampleRadius n) atTop atTop := by
      exact tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    simpa only [zero_mul, Pi.inv_apply] using ht.inv_tendsto_atTop.mul_const ‖T v‖

lemma boundedGenerator_strong (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) {x y : H}
    (hxy : (x,y) ∈ T.graph) :
    Tendsto (fun n : ℕ => boundedGenerator T hs (sampleRadius n) (sampleRadius_ge n) x) atTop (𝓝 y) := by
  simp_rw [regularizer_on_graph T hs _ _ hxy]
  exact regularizer_strong T hs y

def approximatingFlow (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (n : ℕ) (t : ℝ) : H →L[ℂ] H :=
  BoundedFlow.flow (Complex.I • boundedGenerator T hs (sampleRadius n) (sampleRadius_ge n)) t

lemma approximatingFlow_norm (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (n : ℕ) (t : ℝ) (x : H) : ‖approximatingFlow T hs n t x‖ = ‖x‖ := by
  apply BoundedFlow.flow_norm
  exact IsSelfAdjoint.smul_mem_skewAdjoint (by simp [skewAdjoint.mem_iff]) (boundedGenerator_selfAdjoint T hs _ _)

lemma approximatingFlow_opNorm (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (n : ℕ) (t : ℝ) : ‖approximatingFlow T hs n t‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [approximatingFlow_norm,one_mul]

lemma approximatingFlow_difference (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (m n : ℕ) (t : ℝ) (x : H) :
    ‖approximatingFlow T hs m t x-approximatingFlow T hs n t x‖ ≤
      |t| * ‖boundedGenerator T hs (sampleRadius m) (sampleRadius_ge m) x-
        boundedGenerator T hs (sampleRadius n) (sampleRadius_ge n) x‖ := by
  have hm := boundedGenerator_selfAdjoint T hs (sampleRadius m) (sampleRadius_ge m)
  have hn := boundedGenerator_selfAdjoint T hs (sampleRadius n) (sampleRadius_ge n)
  have h := BoundedFlow.flow_difference
    (IsSelfAdjoint.smul_mem_skewAdjoint (r := Complex.I) (by simp [skewAdjoint.mem_iff]) hm)
    (IsSelfAdjoint.smul_mem_skewAdjoint (r := Complex.I) (by simp [skewAdjoint.mem_iff]) hn)
    (((boundedGenerator_commute T hs _ _ _ _).smul_left Complex.I).smul_right Complex.I) t x
  simpa only [approximatingFlow,sub_apply,smul_apply,← smul_sub,norm_smul,Complex.norm_I,one_mul] using h

lemma approximatingFlow_core_cauchy (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (t : ℝ) (x : T.domain) : CauchySeq (fun n => approximatingFlow T hs n t x) := by
  have hx := (boundedGenerator_strong T hs (T.mem_graph_iff.mpr ⟨x,rfl,rfl⟩)).cauchySeq
  rw [Metric.cauchySeq_iff] at hx ⊢
  intro ε hε
  obtain ⟨N,hN⟩ := hx (ε/(|t|+1)) (div_pos hε (by positivity))
  refine ⟨N,fun m hm n hn => ?_⟩
  rw [dist_eq_norm]
  calc
    _ ≤ |t| * ‖boundedGenerator T hs (sampleRadius m) (sampleRadius_ge m) x-
      boundedGenerator T hs (sampleRadius n) (sampleRadius_ge n) x‖ := approximatingFlow_difference T hs _ _ _ _
    _ ≤ (|t|+1) * ‖boundedGenerator T hs (sampleRadius m) (sampleRadius_ge m) x-
      boundedGenerator T hs (sampleRadius n) (sampleRadius_ge n) x‖ := by gcongr; linarith
    _ < (|t|+1)*(ε/(|t|+1)) := by
      apply mul_lt_mul_of_pos_left _ (by positivity)
      simpa only [dist_eq_norm] using hN m hm n hn
    _ = ε := by field_simp

lemma exists_flow_limit (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (t : ℝ) :
    ∃ L : H →L[ℂ] H, ∀ x, Tendsto (fun n => approximatingFlow T hs n t x) atTop (𝓝 (L x)) :=
  StrongLimit.exists_of_dense_core T.domain hs.dense_domain
    (fun n => approximatingFlow T hs n t) (fun n => approximatingFlow_opNorm T hs n t)
    (approximatingFlow_core_cauchy T hs t)

 
def flow (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (t : ℝ) : H →L[ℂ] H :=
  Classical.choose (exists_flow_limit T hs t)

lemma flow_tendsto (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (t : ℝ) (x : H) :
    Tendsto (fun n => approximatingFlow T hs n t x) atTop (𝓝 (flow T hs t x)) :=
  Classical.choose_spec (exists_flow_limit T hs t) x

lemma flow_norm (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (t : ℝ) (x : H) :
    ‖flow T hs t x‖ = ‖x‖ := by
  apply tendsto_nhds_unique (flow_tendsto T hs t x).norm
  simpa only [approximatingFlow_norm] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => ‖x‖) atTop (𝓝 ‖x‖))

lemma flow_zero (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) : flow T hs 0 = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  apply tendsto_nhds_unique (flow_tendsto T hs 0 x)
  simpa only [approximatingFlow,BoundedFlow.flow_zero,one_apply_eq_self] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => x) atTop (𝓝 x))

lemma flow_add (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (s t : ℝ) :
    flow T hs (s+t) = flow T hs s*flow T hs t := by
  apply ContinuousLinearMap.ext
  intro x
  apply tendsto_nhds_unique (flow_tendsto T hs (s+t) x)
  have h := StrongLimit.mul_tendsto (fun n => approximatingFlow T hs n s)
    (fun n => approximatingFlow T hs n t) (flow T hs s) (flow T hs t)
    (fun n => approximatingFlow_opNorm T hs n s) (flow_tendsto T hs s) (flow_tendsto T hs t) x
  simpa only [approximatingFlow,BoundedFlow.flow_add, mul_apply_eq_comp] using h

lemma flow_initial_bound (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) {x y : H}
    (hxy : (x,y) ∈ T.graph) (t : ℝ) : ‖flow T hs t x-x‖ ≤ |t| *‖y‖ := by
  apply le_of_tendsto_of_tendsto ((flow_tendsto T hs t x).sub_const x).norm
    ((boundedGenerator_strong T hs hxy).norm.const_mul |t|)
  filter_upwards [] with n
  have h := BoundedFlow.flow_initial_bound
    (IsSelfAdjoint.smul_mem_skewAdjoint (r := Complex.I) (by simp [skewAdjoint.mem_iff])
      (boundedGenerator_selfAdjoint T hs (sampleRadius n) (sampleRadius_ge n))) t x
  simpa only [approximatingFlow,smul_apply,norm_smul,Complex.norm_I,one_mul] using h

lemma flow_continuous_zero (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (x : H) :
    Tendsto (fun t : ℝ => flow T hs t x) (𝓝 0) (𝓝 x) := by
  have hn : ∀ t, ‖flow T hs t‖ ≤ 1 := by
    intro t
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    rw [flow_norm, one_mul]
  have hc := (StrongLimit.equicontinuous_of_norm_bound _ hn).isClosed_setOfPred_tendsto
    (l := 𝓝 (0 : ℝ)) (f := id) continuous_id
  apply (closure_minimal (s := (T.domain : Set H)) (t := {x | Tendsto
    (fun t : ℝ => flow T hs t x) (𝓝 0) (𝓝 x)}) ?_ hc) (hs.dense_domain x)
  intro v hv
  let w : T.domain := ⟨v,hv⟩
  change Tendsto _ _ _
  rw [← tendsto_sub_nhds_zero_iff]
  apply squeeze_zero_norm (a := fun t : ℝ => |t| *‖T w‖)
  · exact flow_initial_bound T hs (T.mem_graph_iff.mpr ⟨w,rfl,rfl⟩)
  · simpa only [abs_zero,zero_mul] using
      (continuous_abs.continuousAt.tendsto.mul_const ‖T w‖ : Tendsto _ (𝓝 (0 : ℝ)) _)

lemma flow_continuous (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (x : H) :
    Continuous (fun t : ℝ => flow T hs t x) := by
  apply continuous_iff_continuousAt.mpr
  intro s
  have h := (flow T hs s).continuous.tendsto x |>.comp
    ((flow_continuous_zero T hs x).comp (by simpa only [sub_self] using ((tendsto_id : Tendsto (fun t : ℝ => t) (𝓝 s) (𝓝 s)).sub_const s)))
  change Tendsto (fun t : ℝ => flow T hs t x) (𝓝 s) (𝓝 (flow T hs s x))
  change Tendsto (fun t : ℝ => flow T hs s (flow T hs (t-s) x)) _ _ at h
  have he (t : ℝ) : s+(t-s)=t := by ring
  simpa only [← mul_apply_eq_comp,← flow_add,he] using h

lemma approximatingFlow_graph (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (n : ℕ) (t : ℝ) {x y : H} (hxy : (x,y) ∈ T.graph) :
    (approximatingFlow T hs n t x,approximatingFlow T hs n t y) ∈ T.graph := by
  let r := sampleRadius n
  have hr : 1 ≤ r := sampleRadius_ge n
  let z : ℂ := (r : ℂ)*Complex.I
  have hz : 1 ≤ |z.im| := by rw [imaginary_modulus,abs_of_pos (show 0 < r by linarith)]; exact hr
  have hz' : 1 ≤ |(-z).im| := by simpa using hz
  have hc : Commute (boundedGenerator T hs r hr) (resolvent T hs Complex.I (by simp)) := by
    exact ((resolvent_commute T hs z Complex.I hz (by simp)).add_left
      (resolvent_commute T hs (-z) Complex.I hz' (by simp))).smul_left ((r : ℂ)^2/2)
  have hf : Commute (approximatingFlow T hs n t) (resolvent T hs Complex.I (by simp)) :=
    (((hc.smul_left Complex.I).smul_left t).symm.exp_right).symm
  exact graph_invariant_of_commutes_resolvent T hs Complex.I (by simp) _ hf.eq x y hxy

lemma flow_graph (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (t : ℝ)
    {x y : H} (hxy : (x,y) ∈ T.graph) : (flow T hs t x,flow T hs t y) ∈ T.graph := by
  exact hs.isClosed.mem_of_tendsto ((flow_tendsto T hs t x).prodMk_nhds (flow_tendsto T hs t y))
    (Filter.Eventually.of_forall (fun n => approximatingFlow_graph T hs n t hxy))

end StronglyRationalVOA.SymmetricOperator

open scoped Topology
namespace StronglyRationalVOA.BoundedFlow
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma flow_second_order {K : H →L[ℂ] H} (hK : K ∈ skewAdjoint (H →L[ℂ] H))
    (t : ℝ) (x : H) : ‖flow K t x-x-t • K x‖ ≤ |t| ^2*‖K (K x)‖ := by
  have hd : ∀ s : ℝ, HasDerivAt (fun r : ℝ => flow K r x-x-r • K x)
      (flow K s (K x)-K x) s := by
    intro s
    convert ((flow_derivative K s x).sub_const x).sub ((hasDerivAt_id s).smul_const (K x)) using 1
    · rfl
    · simp only [one_smul]
  have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun s : ℝ => flow K s x-x-s • K x) (f' := fun s : ℝ => flow K s (K x)-K x)
    (s := Set.Icc (-|t|) |t|) (x := 0) (y := t)
    (fun s _ => (hd s).hasDerivWithinAt)
    (fun s hs => (flow_initial_bound hK s (K x)).trans
      (mul_le_mul_of_nonneg_right (abs_le.mpr hs) (norm_nonneg _)))
    (convex_Icc _ _) (by simp [abs_nonneg]) (by simp [neg_abs_le,le_abs_self])
  simpa only [flow_zero,one_apply_eq_self,sub_self,zero_smul,sub_zero,Real.norm_eq_abs,
    pow_two,mul_assoc,mul_comm,mul_left_comm] using hb

end StronglyRationalVOA.BoundedFlow

open scoped Topology
open Filter MeasureTheory
namespace StronglyRationalVOA.StrongLimit
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

lemma intervalIntegral_tendsto {F : ℕ → ℝ → H} {f : ℝ → H} {C : ℝ}
    (hc : ∀ n, Continuous (F n)) (hb : ∀ n t, ‖F n t‖ ≤ C)
    (ht : ∀ t, Tendsto (fun n => F n t) atTop (𝓝 (f t))) (a b : ℝ) :
    Tendsto (fun n => ∫ t in a..b, F n t) atTop (𝓝 (∫ t in a..b, f t)) := by
  have h (a b : ℝ) := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (Set.Ioc a b)) (fun _ : ℝ => C)
    (fun n => (hc n).aestronglyMeasurable) (integrable_const C)
    (fun n => Eventually.of_forall (hb n)) (Eventually.of_forall ht)
  exact (h a b).sub (h b a)

end StronglyRationalVOA.StrongLimit

open scoped Topology
open Filter MeasureTheory
namespace StronglyRationalVOA.SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
end StronglyRationalVOA.SymmetricOperator

end

end OAI
