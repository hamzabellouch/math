import OAI.Topology.ArtinGroups.ParabolicIntersections.MeshProjectionInduction

namespace OAI

/-! The actual path projections vanish at a finite quantum cutoff. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V : Type} [Fintype V] (G : SimpleGraph V)

lemma meshProjection_trace_zero (μ : V → ℝ) (δ : ℝ) :
    meshWeightedTrace μ (meshProjection G μ δ 0)=∑ v, (μ v : ℂ) := by
  simp only [meshWeightedTrace,meshProjection_zero,Matrix.trace_one]
  simp only [MeshPaths,Fintype.card_punit,Nat.cast_one,mul_one]

lemma meshProjection_trace_one (μ : V → ℝ) (δ : ℝ)
    (heigen : ∀ v, (∑ u : {u : V // G.Adj u v}, μ u)=δ*μ v) :
    meshWeightedTrace μ (meshProjection G μ δ 1)=(δ : ℂ)*∑ v, (μ v : ℂ) := by
  have hp : meshProjection G μ δ 1=
      meshExtendMatrix G (meshProjection G μ δ 0) := by
    funext v
    rw [meshProjection_one,funext (meshProjection_zero G μ δ),meshExtend_one]
  rw [hp,meshWeightedTrace_extend G μ δ heigen,meshProjection_trace_zero]

lemma meshProjection_trace_step (μ : V → ℝ) (δ : ℝ)
    (heigen : ∀ v, (∑ u : {u : V // G.Adj u v}, μ u)=δ*μ v)
    (n : ℕ) (h : MeshProjectionStage G μ δ (n+1)) :
    meshWeightedTrace μ (meshProjection G μ δ (n+2))=
      (δ : ℂ)*meshWeightedTrace μ (meshProjection G μ δ (n+1))-
        meshWeightedTrace μ (meshProjection G μ δ n) := by
  have ht (v : V) : Matrix.trace (meshProjection G μ δ (n+2) v)=
      Matrix.trace (meshExtendMatrix G (meshProjection G μ δ (n+1)) v)-
        Matrix.trace (meshProjection G μ δ n v) := by
    have hh := h.trace_recurrence (by omega) v
    rw [show n+1-1=n by omega] at hh
    exact hh
  calc
    _ = meshWeightedTrace μ (meshExtendMatrix G (meshProjection G μ δ (n+1)))-
        meshWeightedTrace μ (meshProjection G μ δ n) := by
      simp only [meshWeightedTrace,←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro v _
      rw [ht,mul_sub]
    _ = _ := by rw [meshWeightedTrace_extend G μ δ heigen]

/-- The weighted trace is the quantum integer, without any graph
classification or assumption of mesh nilpotence. -/
theorem meshProjection_weightedTrace (μ : V → ℝ) (hμ : ∀ v, 0<μ v) (δ : ℝ)
    (heigen : ∀ v, (∑ u : {u : V // G.Adj u v}, μ u)=δ*μ v)
    (H : ℕ) (hpos : ∀ n, 0 < n → n < H → 0 < meshQuantum δ n) :
    ∀ n, n<H → meshWeightedTrace μ (meshProjection G μ δ n)=
      (meshQuantum δ (n+1) : ℂ)*∑ v, (μ v : ℂ) := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero =>
    intro _
    simpa only [Nat.zero_add,meshQuantum_one,Complex.ofReal_one,one_mul] using
      meshProjection_trace_zero G μ δ
  | one =>
    intro _
    have hq : meshQuantum δ (1+1)=δ := by norm_num [meshQuantum]
    rw [hq]
    exact meshProjection_trace_one G μ δ heigen
  | more n ih ih₁ =>
    intro hn
    have hs := meshProjectionStage_before_cutoff G μ hμ δ heigen H hpos (n+1) hn
    rw [meshProjection_trace_step G μ δ heigen n hs,ih₁ (by omega),ih (by omega)]
    have hq : meshQuantum δ (n+2+1)=δ*meshQuantum δ (n+1+1)-meshQuantum δ (n+1) :=
      meshQuantum_step δ (n+1)
    rw [hq,Complex.ofReal_sub,Complex.ofReal_mul]
    ring

/-- Some positive length has zero path projection. This is the finite
essential-path bound, proved from a positive adjacency eigenvector below 2. -/
theorem meshProjection_eventually_zero (μ : V → ℝ) (hμ : ∀ v, 0<μ v)
    (δ : ℝ) (hδ0 : 0<δ) (hδ2 : δ<2)
    (heigen : ∀ v, (∑ u : {u : V // G.Adj u v}, μ u)=δ*μ v) :
    ∃ N : ℕ, 0<N ∧ ∀ v, meshProjection G μ δ N v=0 := by
  obtain ⟨H,hH,hq,hpos⟩ := meshQuantum_cutoff δ hδ0 hδ2
  let N := H-1
  have hN : 0<N := by dsimp [N]; omega
  have hNH : N<H := by dsimp [N]; omega
  have hstage := meshProjectionStage_before_cutoff G μ hμ δ heigen H hpos (H-2) (by omega)
  have hlen : H-2+1=N := by dsimp [N]; omega
  have hstar : ∀ v, (meshProjection G μ δ N v).conjTranspose=meshProjection G μ δ N v := by
    rw [←hlen]
    exact hstage.upper_star
  have hsq : ∀ v, meshProjection G μ δ N v*meshProjection G μ δ N v=
      meshProjection G μ δ N v := by
    rw [←hlen]
    exact hstage.upper_square
  have hw := meshProjection_weightedTrace G μ hμ δ heigen H hpos N hNH
  rw [show N+1=H by dsimp [N]; omega] at hw
  have hnonneg := meshWeightedTrace_nonneg μ (fun v => (hμ v).le)
    (meshProjection G μ δ N) hstar hsq
  have hnonpos : (meshWeightedTrace μ (meshProjection G μ δ N)).re≤0 := by
    rw [hw]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
      Complex.re_sum]
    exact mul_nonpos_of_nonpos_of_nonneg hq (Finset.sum_nonneg (fun v _ => (hμ v).le))
  have him : (meshWeightedTrace μ (meshProjection G μ δ N)).im=0 := by
    rw [hw]
    simp
  have hz : meshWeightedTrace μ (meshProjection G μ δ N)=0 :=
    Complex.ext (le_antisymm hnonpos hnonneg) him
  exact ⟨N,hN,meshWeightedTrace_zero μ hμ (meshProjection G μ δ N) hstar hsq hz⟩

end HarmonicArtin.ParabolicIntersections

end OAI
