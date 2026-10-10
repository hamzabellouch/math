import Mathlib
import OAI.RepresentationTheory.SignedTensor.Blocks
import OAI.RepresentationTheory.Unitary.Spectral

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ComplexConjugate Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CoordinateSweeps.TensorBoard
variable {R C J : Type*} [Fintype R] [DecidableEq R] [Nonempty R]
  [Fintype C] [DecidableEq C] [Fintype J] [DecidableEq J]

omit [Nonempty R] in
lemma board_trace_le_reindexed {l : ℕ} (F : Finset (R × C)) (e : Fin l ≃ F)
    (r : R → Matrix J J ℂ) (v : C → Matrix J J ℂ)
    (hr : ∀ i, (r i).PosSemidef) (hv : ∀ j, (v j).PosSemidef)
    (ht : ∀ j, Matrix.trace (v j)=1) (A : Matrix J J ℂ) (hA : A.IsHermitian)
    (hw : ((Fintype.card R : ℂ) • (1 : Matrix J J ℂ)-∑ i, A*r i*A).PosSemidef) :
    (Matrix.trace (tensor (fun _ : Fin l => A)*tensor (fun x => r (e x).val.1)*
      tensor (fun _ : Fin l => A)*tensor (fun x => v (e x).val.2))).re ≤
        Real.exp (Fintype.card R*Fintype.card C-F.card) := by
  have hh := board_trace_le F r v hr hv ht A hA hw
  rw [← tensor_mul,tensor_trace] at hh
  rw [← tensor_mul,← tensor_mul,← tensor_mul,tensor_trace]
  have he := Equiv.prod_comp e (fun x : F => Matrix.trace (A*r x.val.1*A*v x.val.2))
  simpa only [he] using hh

end CoordinateSweeps.TensorBoard

namespace CoordinateSweeps.UnitaryIrrep
variable {Γ n : Type*} [Group Γ] [Fintype Γ] [Fintype n] [DecidableEq n]
lemma projector_commute_lift (ρ : UnitaryIrrep Γ) (τ : Γ →* Matrix n n ℂ)
    (x : MonoidAlgebra ℂ Γ) :
    ρ.projector τ*MonoidAlgebra.lift ℂ _ _ τ x=MonoidAlgebra.lift ℂ _ _ τ x*ρ.projector τ := by
  induction x using MonoidAlgebra.induction_on with
  | of g => simpa using (ρ.projector_commute τ g).symm
  | add x y hx hy => simp only [map_add,add_mul,mul_add,hx,hy]
  | smul c x hx => simp only [map_smul,smul_mul_assoc,mul_smul_comm,hx]
end CoordinateSweeps.UnitaryIrrep

namespace CoordinateSweeps.SignedTensor

lemma densityPower_commute_projector {p l : ℕ} (r : Matrix (Letter p) (Letter p) ℂ)
    (hr : IsEven r) (ρ : UnitaryIrrep (Equiv.Perm (Fin l))) :
    densityPower l r*ρ.projector (action p l)=ρ.projector (action p l)*densityPower l r := by
  simp only [UnitaryIrrep.projector,Matrix.mul_sum,Matrix.sum_mul,Matrix.mul_smul,Matrix.smul_mul]
  apply Finset.sum_congr rfl
  intro σ hσ
  exact congrArg (fun A => ρ.coefficient σ • A) (densityPower_commute_of_even r hr σ).symm

lemma even_average_trace {R : Type*} [Fintype R] [Nonempty R] {p : ℕ}
    (r : R → EvenDensity p) (ε : ℝ) :
    Matrix.trace ((Fintype.card R : ℂ)⁻¹ • (∑ i, (r i).val)+
      (ε : ℂ) • (1 : Matrix (Letter p) (Letter p) ℂ)) = 1+ε*(2*p) := by
  rw [Matrix.trace_add,Matrix.trace_smul,Matrix.trace_sum,Matrix.trace_smul,Matrix.trace_one]
  simp only [(r _).property.2.1,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,
    smul_eq_mul,Fintype.card_fin]
  have hc : (Fintype.card R : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [inv_mul_cancel₀ hc]
  push_cast
  rfl

end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.SignedTensor
open TensorBoard Overlap
variable {R C I J : Type*} [Fintype R] [DecidableEq R] [Nonempty R]
  [Fintype C] [DecidableEq C] [Fintype I] [Fintype J]

abbrev groupOperator {p l : ℕ} (x : MonoidAlgebra ℂ (Equiv.Perm (Fin l))) :
    Matrix (Word p l) (Word p l) ℂ := MonoidAlgebra.lift ℂ _ _ (action p l) x

def rowProduct {p l : ℕ} {F : Finset (R × C)} (e : Fin l ≃ F) (r : R → EvenDensity p) :
    Matrix (Word p l) (Word p l) ℂ := TensorBoard.tensor (fun x => (r (e x).val.1).val)

def columnProduct {p l : ℕ} {F : Finset (R × C)} (e : Fin l ≃ F) (r : C → EvenDensity p) :
    Matrix (Word p l) (Word p l) ℂ := TensorBoard.tensor (fun x => (r (e x).val.2).val)

/- Literal deleted-board overlap with actual signed tensor action. The two
mixture dominations will be obtained by tensoring the local density theorem;
the whitening and the full-group dimension loss are constructed here. -/
theorem board_overlap_regularized {p l : ℕ} (hp : 0 < p)
    (F : Finset (R × C)) (e : Fin l ≃ F)
    (ρ : UnitaryIrrep (Equiv.Perm (Fin l)))
    (PR : Matrix (Word p l) (Word p l) ℂ) (xC : MonoidAlgebra ℂ (Equiv.Perm (Fin l)))
    (hPR : PR.IsHermitian) (hPR2 : PR*PR=PR)
    (hPC : (groupOperator (p := p) xC).IsHermitian)
    (hPC2 : groupOperator (p := p) xC*groupOperator (p := p) xC=groupOperator (p := p) xC)
    (u : I → ℝ) (v : J → ℝ) (hu : ∀ i, 0 ≤ u i) (hv : ∀ j, 0 ≤ v j)
    (hsu : ∑ i, u i=1) (hsv : ∑ j, v j=1)
    (r : I → R → EvenDensity p) (c : J → C → EvenDensity p)
    (cr cc : ℝ) (hcr : 0 ≤ cr) (hcc : 0 ≤ cc)
    (hrow : ((cr : ℂ) • (∑ i, (u i : ℂ) • rowProduct e (r i))-PR).PosSemidef)
    (hcol : ((cc : ℂ) • (∑ j, (v j : ℂ) • columnProduct e (c j))-groupOperator xC).PosSemidef)
    {ε : ℝ} (hε : 0 < ε) :
    (ρ.dimension : ℝ)*‖groupOperator (p := p) xC*ρ.projector (action p l)*PR‖^2 ≤
      cr*cc*(1+ε*(2*p : ℕ))^l*Real.exp (Fintype.card R*Fintype.card C-F.card) := by
  let : NeZero (2*p) := ⟨by omega⟩
  let τ := action p l
  let PC := groupOperator (p := p) xC
  let B (i : I) : Matrix (Letter p) (Letter p) ℂ :=
    (Fintype.card R : ℂ)⁻¹ • (∑ k, (r i k).val)+(ε : ℂ) • 1
  choose A hA hAe hABA hAw using fun i => exists_even_whitening (r i) hε
  have hb (i : I) : (B i).PosSemidef :=
    (average_regularization_posDef (fun k => (r i k).val) (fun k => (r i k).property.1) hε).posSemidef
  have he (i : I) : IsEven (B i) := isEven_add
    (isEven_smul _ (isEven_sum _ (fun k => (r i k).property.2.2))) (isEven_smul _ isEven_one)
  have htau (g : Equiv.Perm (Fin l)) : (τ g).conjTranspose=τ g⁻¹ := (matrix_inv g).symm
  have hpq : ρ.projector τ*PC=PC*ρ.projector τ := ρ.projector_commute_lift τ xC
  have htt : 0 ≤ (1+ε*(2*p : ℕ))^l := pow_nonneg (by positivity) _
  have hwhite (i : I) :
      (((1+ε*(2*p : ℕ))^l : ℝ) : ℂ) • (densityPower l (A i)*PC*densityPower l (A i)) -
        (ρ.dimension : ℂ) • (PC*ρ.projector τ) |>.PosSemidef := by
    have hWA : (densityPower l (A i)).IsHermitian := (densityPower_posSemidef l (A i) (hA i)).isHermitian
    have hWABA : densityPower l (A i)*densityPower l (B i)*densityPower l (A i)=1 := by
      rw [← densityPower_mul,← densityPower_mul,hABA i,densityPower_one]
    have hh := Overlap.whitened_projector_domination ρ τ htau
      (densityPower l (B i)) (densityPower l (A i)) PC (densityPower_posSemidef l (B i) (hb i))
      (fun g => densityPower_commute_of_even (B i) (he i) g) hWA hWABA
      (densityPower_commute_projector (A i) (hAe i) ρ)
      (densityPower_commute_lift (A i) (hAe i) xC).symm hPC hPC2 hpq
    have ht : Matrix.trace (densityPower l (B i))=(((1+ε*(2*p : ℕ))^l : ℝ) : ℂ) := by
      rw [densityPower_trace,even_average_trace]
      push_cast
      rfl
    rwa [ht] at hh
  apply Overlap.finite_mixture_overlap PR PC (ρ.projector τ) hPR hPR2 hPC hPC2
    (ρ.projector_hermitian τ htau) (ρ.projector_idempotent τ) hpq u v hu hv hsu hsv
    (fun i => rowProduct e (r i)) (fun j => columnProduct e (c j)) (fun i => densityPower l (A i))
    (fun i => TensorBoard.tensor_posSemidef _ (fun x => (r i (e x).val.1).property.1))
    (fun i => (densityPower_posSemidef l (A i) (hA i)).isHermitian)
    cr cc ρ.dimension ((1+ε*(2*p : ℕ))^l) _ hcr hcc (Nat.cast_nonneg _) htt hrow hcol hwhite
  intro i j
  exact board_trace_le_reindexed F e (fun k => (r i k).val) (fun k => (c j k).val)
    (fun k => (r i k).property.1) (fun k => (c j k).property.1) (fun k => (c j k).property.2.1)
    (A i) (hA i).isHermitian (hAw i)

end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.SignedTensor
open TensorBoard Overlap
variable {R C I J : Type*} [Fintype R] [DecidableEq R] [Nonempty R]
  [Fintype C] [DecidableEq C] [Fintype I] [Fintype J]

theorem board_overlap {p l : ℕ} (hp : 0 < p)
    (F : Finset (R × C)) (e : Fin l ≃ F)
    (ρ : UnitaryIrrep (Equiv.Perm (Fin l)))
    (PR : Matrix (Word p l) (Word p l) ℂ) (xC : MonoidAlgebra ℂ (Equiv.Perm (Fin l)))
    (hPR : PR.IsHermitian) (hPR2 : PR*PR=PR)
    (hPC : (groupOperator (p := p) xC).IsHermitian)
    (hPC2 : groupOperator (p := p) xC*groupOperator (p := p) xC=groupOperator (p := p) xC)
    (u : I → ℝ) (v : J → ℝ) (hu : ∀ i, 0 ≤ u i) (hv : ∀ j, 0 ≤ v j)
    (hsu : ∑ i, u i=1) (hsv : ∑ j, v j=1)
    (r : I → R → EvenDensity p) (c : J → C → EvenDensity p)
    (cr cc : ℝ) (hcr : 0 ≤ cr) (hcc : 0 ≤ cc)
    (hrow : ((cr : ℂ) • (∑ i, (u i : ℂ) • rowProduct e (r i))-PR).PosSemidef)
    (hcol : ((cc : ℂ) • (∑ j, (v j : ℂ) • columnProduct e (c j))-groupOperator xC).PosSemidef)
 :
    (ρ.dimension : ℝ)*‖groupOperator (p := p) xC*ρ.projector (action p l)*PR‖^2 ≤
      cr*cc*Real.exp (Fintype.card R*Fintype.card C-F.card) := by
  let f (ε : ℝ) := cr*cc*(1+ε*(2*p : ℕ))^l*Real.exp (Fintype.card R*Fintype.card C-F.card)
  have hf : Continuous f := by fun_prop
  have hh : ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0),
      (ρ.dimension : ℝ)*‖groupOperator (p := p) xC*ρ.projector (action p l)*PR‖^2 ≤ f ε := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact board_overlap_regularized hp F e ρ PR xC hPR hPR2 hPC hPC2
      u v hu hv hsu hsv r c cr cc hcr hcc hrow hcol hε
  have hh' := ge_of_tendsto (hf.continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds : nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds 0)) hh
  simpa [f] using hh'

end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.SignedTensor
open TensorBoard
variable {p r c : ℕ} [NeZero r]

/- Source 06:eq19 for literal row and column subgroup projectors on an
arbitrary board with holes. The mixtures and signed regroupings are constructed. -/
theorem actual_board_overlap (F : Finset (Fin r × Fin c))
    (e : Fin (Fintype.card F) ≃ F) (s : ℕ) (hp : 0 < p) (hps : p ≤ s)
    (hnR : ∀ i, FiberBlocks.size (fun x : F => x.val.1) i ≤ s)
    (hnC : ∀ j, FiberBlocks.size (fun x : F => x.val.2) j ≤ s)
    (ρR : ∀ i, UnitaryIrrep (Equiv.Perm (Fin (FiberBlocks.size (fun x : F => x.val.1) i))))
    (ρC : ∀ j, UnitaryIrrep (Equiv.Perm (Fin (FiberBlocks.size (fun x : F => x.val.2) j))))
    (ρ : UnitaryIrrep (Equiv.Perm (Fin (Fintype.card F)))) :
    (ρ.dimension : ℝ)*‖fiberProjector (p := p) (fun x : F => x.val.2) e ρC*
      ρ.projector (action p (Fintype.card F))*fiberProjector (fun x : F => x.val.1) e ρR‖^2 ≤
        ((∏ i, ((ρR i).dimension : ℝ))*(s+1 : ℕ)^(r*(41*p^2)))*
        ((∏ j, ((ρC j).dimension : ℝ))*(s+1 : ℕ)^(c*(41*p^2)))*
        Real.exp (r*c-F.card) := by
  obtain ⟨I,hI,nI,a,ha⟩ := finite_fiber_density_domination (fun x : F => x.val.1) e s hp hps hnR ρR
  obtain ⟨J,hJ,nJ,b,hb⟩ := finite_fiber_density_domination (fun x : F => x.val.2) e s hp hps hnC ρC
  let := hI
  let := hJ
  let := nI
  let := nJ
  have hI0 : (Fintype.card I : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hJ0 : (Fintype.card J : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hu : ∑ _ : I, (Fintype.card I : ℝ)⁻¹=1 := by
    rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_inv_cancel₀ hI0]
  have hv : ∑ _ : J, (Fintype.card J : ℝ)⁻¹=1 := by
    rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_inv_cancel₀ hJ0]
  have hr := fiberProjector_posSemidef (p := p) (fun x : F => x.val.1) e ρR
  have hc := fiberProjector_posSemidef (p := p) (fun x : F => x.val.2) e ρC
  have hr2 := fiberProjector_idempotent (p := p) (fun x : F => x.val.1) e ρR
  have hc2 := fiberProjector_idempotent (p := p) (fun x : F => x.val.2) e ρC
  let xC := fiberProjectorAlgebra (fun x : F => x.val.2) e ρC
  have hx : groupOperator (p := p) xC=fiberProjector (p := p) (fun x : F => x.val.2) e ρC :=
    fiberProjectorAlgebra_lift _ _ _
  have hrow : (((∏ i, ((ρR i).dimension : ℝ))*(s+1 : ℕ)^(r*(41*p^2)) : ℝ) : ℂ) •
      (∑ i : I, (((Fintype.card I : ℝ)⁻¹ : ℝ) : ℂ) • rowProduct e (a i))-
        fiberProjector (p := p) (fun x : F => x.val.1) e ρR |>.PosSemidef := by
    simpa only [Complex.ofReal_mul,Complex.ofReal_prod,Complex.ofReal_natCast,Complex.ofReal_pow,
      Complex.ofReal_inv,← Finset.smul_sum,rowProduct] using ha
  have hcol : (((∏ j, ((ρC j).dimension : ℝ))*(s+1 : ℕ)^(c*(41*p^2)) : ℝ) : ℂ) •
      (∑ j : J, (((Fintype.card J : ℝ)⁻¹ : ℝ) : ℂ) • columnProduct e (b j))-
        groupOperator (p := p) xC |>.PosSemidef := by
    rw [hx]
    simpa only [Complex.ofReal_mul,Complex.ofReal_prod,Complex.ofReal_natCast,Complex.ofReal_pow,
      Complex.ofReal_inv,← Finset.smul_sum,columnProduct] using hb
  have hh := board_overlap hp F e ρ _ xC hr.isHermitian hr2 (hx ▸ hc.isHermitian)
    (by rw [hx]; exact hc2) (fun _ : I => (Fintype.card I : ℝ)⁻¹)
    (fun _ : J => (Fintype.card J : ℝ)⁻¹) (fun _ => by positivity) (fun _ => by positivity)
    hu hv a b ((∏ i, ((ρR i).dimension : ℝ))*(s+1 : ℕ)^(r*(41*p^2)))
    ((∏ j, ((ρC j).dimension : ℝ))*(s+1 : ℕ)^(c*(41*p^2))) (by positivity) (by positivity) hrow hcol
  simpa only [hx,Fintype.card_fin] using hh

end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.TensorBoard
variable {R C J : Type*} [Fintype R] [DecidableEq R] [Nonempty R]
  [Fintype C] [DecidableEq C] [Fintype J] [DecidableEq J]
omit [Nonempty R] in
lemma board_trace_le_labels {l : ℕ} (e : Fin l → R × C) (he : Function.Injective e)
    (r : R → Matrix J J ℂ) (v : C → Matrix J J ℂ)
    (hr : ∀ i, (r i).PosSemidef) (hv : ∀ j, (v j).PosSemidef)
    (ht : ∀ j, Matrix.trace (v j)=1) (A : Matrix J J ℂ) (hA : A.IsHermitian)
    (hw : ((Fintype.card R : ℂ) • (1 : Matrix J J ℂ)-∑ i, A*r i*A).PosSemidef) :
    (Matrix.trace (tensor (fun _ : Fin l => A)*tensor (fun x => r (e x).1)*
      tensor (fun _ : Fin l => A)*tensor (fun x => v (e x).2))).re ≤
        Real.exp (Fintype.card R*Fintype.card C-l) := by
  let F : Finset (R × C) := Finset.univ.image e
  let E : Fin l ≃ F := Equiv.ofBijective (fun x => ⟨e x,by simp [F]⟩) (by
    constructor
    · intro x y h; exact he (congrArg Subtype.val h)
    · intro y
      obtain ⟨x,_,hx⟩ := Finset.mem_image.mp y.property
      exact ⟨x,Subtype.ext hx⟩)
  have hc : F.card=l := by
    dsimp [F]
    rw [Finset.card_image_of_injective _ he,Finset.card_univ,Fintype.card_fin]
  have hh := board_trace_le_reindexed F E r v hr hv ht A hA hw
  have hE (x : Fin l) : (E x).val=e x := rfl
  simpa only [hE,hc] using hh
end CoordinateSweeps.TensorBoard

namespace CoordinateSweeps.SignedTensor
open TensorBoard
variable {R C I J : Type*} [Fintype R] [DecidableEq R] [Nonempty R]
  [Fintype C] [DecidableEq C] [Fintype I] [Fintype J]

def labelRowProduct {p l : ℕ} (e : Fin l → R × C) (r : R → EvenDensity p) :
    Matrix (Word p l) (Word p l) ℂ := TensorBoard.tensor (fun x => (r (e x).1).val)

def labelColumnProduct {p l : ℕ} (e : Fin l → R × C) (r : C → EvenDensity p) :
    Matrix (Word p l) (Word p l) ℂ := TensorBoard.tensor (fun x => (r (e x).2).val)

/- Literal deleted-board overlap with actual signed tensor action. The two
mixture dominations will be obtained by tensoring the local density theorem;
the whitening and the full-group dimension loss are constructed here. -/
theorem label_board_overlap_regularized {p l : ℕ} (hp : 0 < p)
    (e : Fin l → R × C) (hinj : Function.Injective e)
    (ρ : UnitaryIrrep (Equiv.Perm (Fin l)))
    (PR : Matrix (Word p l) (Word p l) ℂ) (xC : MonoidAlgebra ℂ (Equiv.Perm (Fin l)))
    (hPR : PR.IsHermitian) (hPR2 : PR*PR=PR)
    (hPC : (groupOperator (p := p) xC).IsHermitian)
    (hPC2 : groupOperator (p := p) xC*groupOperator (p := p) xC=groupOperator (p := p) xC)
    (u : I → ℝ) (v : J → ℝ) (hu : ∀ i, 0 ≤ u i) (hv : ∀ j, 0 ≤ v j)
    (hsu : ∑ i, u i=1) (hsv : ∑ j, v j=1)
    (r : I → R → EvenDensity p) (c : J → C → EvenDensity p)
    (cr cc : ℝ) (hcr : 0 ≤ cr) (hcc : 0 ≤ cc)
    (hrow : ((cr : ℂ) • (∑ i, (u i : ℂ) • labelRowProduct e (r i))-PR).PosSemidef)
    (hcol : ((cc : ℂ) • (∑ j, (v j : ℂ) • labelColumnProduct e (c j))-groupOperator xC).PosSemidef)
    {ε : ℝ} (hε : 0 < ε) :
    (ρ.dimension : ℝ)*‖groupOperator (p := p) xC*ρ.projector (action p l)*PR‖^2 ≤
      cr*cc*(1+ε*(2*p : ℕ))^l*Real.exp (Fintype.card R*Fintype.card C-l) := by
  let : NeZero (2*p) := ⟨by omega⟩
  let τ := action p l
  let PC := groupOperator (p := p) xC
  let B (i : I) : Matrix (Letter p) (Letter p) ℂ :=
    (Fintype.card R : ℂ)⁻¹ • (∑ k, (r i k).val)+(ε : ℂ) • 1
  choose A hA hAe hABA hAw using fun i => exists_even_whitening (r i) hε
  have hb (i : I) : (B i).PosSemidef :=
    (average_regularization_posDef (fun k => (r i k).val) (fun k => (r i k).property.1) hε).posSemidef
  have he (i : I) : IsEven (B i) := isEven_add
    (isEven_smul _ (isEven_sum _ (fun k => (r i k).property.2.2))) (isEven_smul _ isEven_one)
  have htau (g : Equiv.Perm (Fin l)) : (τ g).conjTranspose=τ g⁻¹ := (matrix_inv g).symm
  have hpq : ρ.projector τ*PC=PC*ρ.projector τ := ρ.projector_commute_lift τ xC
  have htt : 0 ≤ (1+ε*(2*p : ℕ))^l := pow_nonneg (by positivity) _
  have hwhite (i : I) :
      (((1+ε*(2*p : ℕ))^l : ℝ) : ℂ) • (densityPower l (A i)*PC*densityPower l (A i)) -
        (ρ.dimension : ℂ) • (PC*ρ.projector τ) |>.PosSemidef := by
    have hWA : (densityPower l (A i)).IsHermitian := (densityPower_posSemidef l (A i) (hA i)).isHermitian
    have hWABA : densityPower l (A i)*densityPower l (B i)*densityPower l (A i)=1 := by
      rw [← densityPower_mul,← densityPower_mul,hABA i,densityPower_one]
    have hh := Overlap.whitened_projector_domination ρ τ htau
      (densityPower l (B i)) (densityPower l (A i)) PC (densityPower_posSemidef l (B i) (hb i))
      (fun g => densityPower_commute_of_even (B i) (he i) g) hWA hWABA
      (densityPower_commute_projector (A i) (hAe i) ρ)
      (densityPower_commute_lift (A i) (hAe i) xC).symm hPC hPC2 hpq
    have ht : Matrix.trace (densityPower l (B i))=(((1+ε*(2*p : ℕ))^l : ℝ) : ℂ) := by
      rw [densityPower_trace,even_average_trace]
      push_cast
      rfl
    rwa [ht] at hh
  apply Overlap.finite_mixture_overlap PR PC (ρ.projector τ) hPR hPR2 hPC hPC2
    (ρ.projector_hermitian τ htau) (ρ.projector_idempotent τ) hpq u v hu hv hsu hsv
    (fun i => labelRowProduct e (r i)) (fun j => labelColumnProduct e (c j)) (fun i => densityPower l (A i))
    (fun i => TensorBoard.tensor_posSemidef _ (fun x => (r i (e x).1).property.1))
    (fun i => (densityPower_posSemidef l (A i) (hA i)).isHermitian)
    cr cc ρ.dimension ((1+ε*(2*p : ℕ))^l) _ hcr hcc (Nat.cast_nonneg _) htt hrow hcol hwhite
  intro i j
  exact board_trace_le_labels e hinj (fun k => (r i k).val) (fun k => (c j k).val)
    (fun k => (r i k).property.1) (fun k => (c j k).property.1) (fun k => (c j k).property.2.1)
    (A i) (hA i).isHermitian (hAw i)

end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.SignedTensor
open TensorBoard Overlap
variable {R C I J : Type*} [Fintype R] [DecidableEq R] [Nonempty R]
  [Fintype C] [DecidableEq C] [Fintype I] [Fintype J]

theorem label_board_overlap {p l : ℕ} (hp : 0 < p)
    (e : Fin l → R × C) (hinj : Function.Injective e)
    (ρ : UnitaryIrrep (Equiv.Perm (Fin l)))
    (PR : Matrix (Word p l) (Word p l) ℂ) (xC : MonoidAlgebra ℂ (Equiv.Perm (Fin l)))
    (hPR : PR.IsHermitian) (hPR2 : PR*PR=PR)
    (hPC : (groupOperator (p := p) xC).IsHermitian)
    (hPC2 : groupOperator (p := p) xC*groupOperator (p := p) xC=groupOperator (p := p) xC)
    (u : I → ℝ) (v : J → ℝ) (hu : ∀ i, 0 ≤ u i) (hv : ∀ j, 0 ≤ v j)
    (hsu : ∑ i, u i=1) (hsv : ∑ j, v j=1)
    (r : I → R → EvenDensity p) (c : J → C → EvenDensity p)
    (cr cc : ℝ) (hcr : 0 ≤ cr) (hcc : 0 ≤ cc)
    (hrow : ((cr : ℂ) • (∑ i, (u i : ℂ) • labelRowProduct e (r i))-PR).PosSemidef)
    (hcol : ((cc : ℂ) • (∑ j, (v j : ℂ) • labelColumnProduct e (c j))-groupOperator xC).PosSemidef)
 :
    (ρ.dimension : ℝ)*‖groupOperator (p := p) xC*ρ.projector (action p l)*PR‖^2 ≤
      cr*cc*Real.exp (Fintype.card R*Fintype.card C-l) := by
  let f (ε : ℝ) := cr*cc*(1+ε*(2*p : ℕ))^l*Real.exp (Fintype.card R*Fintype.card C-l)
  have hf : Continuous f := by fun_prop
  have hh : ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0),
      (ρ.dimension : ℝ)*‖groupOperator (p := p) xC*ρ.projector (action p l)*PR‖^2 ≤ f ε := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact label_board_overlap_regularized hp e hinj ρ PR xC hPR hPR2 hPC hPC2
      u v hu hv hsu hsv r c cr cc hcr hcc hrow hcol hε
  have hh' := ge_of_tendsto (hf.continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds : nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds 0)) hh
  simpa [f] using hh'

end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.SignedTensor
open TensorBoard
variable {p r c : ℕ} [NeZero r]
  {L : Type*} [Fintype L] [DecidableEq L]

/- Source 06:eq19 for literal row and column subgroup projectors on an
arbitrary board with holes. The mixtures and signed regroupings are constructed. -/
omit [DecidableEq L] in
theorem actual_label_overlap (f : L → Fin r) (g : L → Fin c)
    (hinj : Function.Injective (fun x => (f x,g x)))
    (e : Fin (Fintype.card L) ≃ L) (s : ℕ) (hp : 0 < p) (hps : p ≤ s)
    (hnR : ∀ i, FiberBlocks.size f i ≤ s)
    (hnC : ∀ j, FiberBlocks.size g j ≤ s)
    (ρR : ∀ i, UnitaryIrrep (Equiv.Perm (Fin (FiberBlocks.size f i))))
    (ρC : ∀ j, UnitaryIrrep (Equiv.Perm (Fin (FiberBlocks.size g j))))
    (ρ : UnitaryIrrep (Equiv.Perm (Fin (Fintype.card L)))) :
    (ρ.dimension : ℝ)*‖fiberProjector (p := p) g e ρC*
      ρ.projector (action p (Fintype.card L))*fiberProjector f e ρR‖^2 ≤
        ((∏ i, ((ρR i).dimension : ℝ))*(s+1 : ℕ)^(r*(41*p^2)))*
        ((∏ j, ((ρC j).dimension : ℝ))*(s+1 : ℕ)^(c*(41*p^2)))*
        Real.exp (r*c-Fintype.card L) := by
  obtain ⟨I,hI,nI,a,ha⟩ := finite_fiber_density_domination f e s hp hps hnR ρR
  obtain ⟨J,hJ,nJ,b,hb⟩ := finite_fiber_density_domination g e s hp hps hnC ρC
  let := hI
  let := hJ
  let := nI
  let := nJ
  have hI0 : (Fintype.card I : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hJ0 : (Fintype.card J : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hu : ∑ _ : I, (Fintype.card I : ℝ)⁻¹=1 := by
    rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_inv_cancel₀ hI0]
  have hv : ∑ _ : J, (Fintype.card J : ℝ)⁻¹=1 := by
    rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_inv_cancel₀ hJ0]
  have hr := fiberProjector_posSemidef (p := p) f e ρR
  have hc := fiberProjector_posSemidef (p := p) g e ρC
  have hr2 := fiberProjector_idempotent (p := p) f e ρR
  have hc2 := fiberProjector_idempotent (p := p) g e ρC
  let xC := fiberProjectorAlgebra g e ρC
  have hx : groupOperator (p := p) xC=fiberProjector (p := p) g e ρC :=
    fiberProjectorAlgebra_lift _ _ _
  have hrow : (((∏ i, ((ρR i).dimension : ℝ))*(s+1 : ℕ)^(r*(41*p^2)) : ℝ) : ℂ) •
      (∑ i : I, (((Fintype.card I : ℝ)⁻¹ : ℝ) : ℂ) • labelRowProduct (fun x => (f (e x),g (e x))) (a i))-
        fiberProjector (p := p) f e ρR |>.PosSemidef := by
    simpa only [Complex.ofReal_mul,Complex.ofReal_prod,Complex.ofReal_natCast,Complex.ofReal_pow,
      Complex.ofReal_inv,← Finset.smul_sum,labelRowProduct] using ha
  have hcol : (((∏ j, ((ρC j).dimension : ℝ))*(s+1 : ℕ)^(c*(41*p^2)) : ℝ) : ℂ) •
      (∑ j : J, (((Fintype.card J : ℝ)⁻¹ : ℝ) : ℂ) • labelColumnProduct (fun x => (f (e x),g (e x))) (b j))-
        groupOperator (p := p) xC |>.PosSemidef := by
    rw [hx]
    simpa only [Complex.ofReal_mul,Complex.ofReal_prod,Complex.ofReal_natCast,Complex.ofReal_pow,
      Complex.ofReal_inv,← Finset.smul_sum,labelColumnProduct] using hb
  have hh := label_board_overlap hp (fun x => (f (e x),g (e x))) (hinj.comp e.injective) ρ _ xC hr.isHermitian hr2 (hx ▸ hc.isHermitian)
    (by rw [hx]; exact hc2) (fun _ : I => (Fintype.card I : ℝ)⁻¹)
    (fun _ : J => (Fintype.card J : ℝ)⁻¹) (fun _ => by positivity) (fun _ => by positivity)
    hu hv a b ((∏ i, ((ρR i).dimension : ℝ))*(s+1 : ℕ)^(r*(41*p^2)))
    ((∏ j, ((ρC j).dimension : ℝ))*(s+1 : ℕ)^(c*(41*p^2))) (by positivity) (by positivity) hrow hcol
  simpa only [hx,Fintype.card_fin] using hh

end CoordinateSweeps.SignedTensor

end
end
end
end
end
end
end
end
open scoped Matrix.Norms.L2Operator

end OAI
