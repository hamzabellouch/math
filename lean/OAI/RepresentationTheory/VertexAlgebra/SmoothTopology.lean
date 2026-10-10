import OAI.RepresentationTheory.VertexAlgebra.PropagatorContinuation

namespace OAI

noncomputable section
open Filter Set
open scoped Topology ContDiff
namespace StronglyRationalVOA.PositiveCircleGeometry.SmoothLift

def identity : SmoothLift where
  toFun := id
  add_one := fun _ => rfl
  smooth := contDiff_id
  derivative_pos := by intro x; simp
@[simp] lemma identity_apply (x : ℝ) : identity x=x := rfl

def jet (φ : SmoothLift) (k : ℕ) : C(ℝ,ℝ) :=
  ⟨iteratedDeriv k φ, φ.smooth.continuous_iteratedDeriv k (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))⟩

instance : TopologicalSpace SmoothLift :=
  TopologicalSpace.induced (fun φ => jet φ) inferInstance

lemma continuous_jet (k : ℕ) : Continuous (fun φ : SmoothLift => jet φ k) :=
  (continuous_apply k).comp (show Continuous (fun φ : SmoothLift => jet φ) from continuous_induced_dom)

 
def identityError (φ : SmoothLift) : ℝ :=
  ∑ k ∈ Finset.range 5, ‖(jet φ k-jet identity k).restrict (Icc (0:ℝ) 1)‖

lemma identityError_nonneg (φ : SmoothLift) : 0 ≤ identityError φ :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

lemma continuous_identityError : Continuous identityError := by
  apply continuous_finsetSum
  intro k _
  exact ((ContinuousMap.continuous_restrict _).comp
    ((continuous_jet k).sub continuous_const)).norm

@[simp] lemma identityError_identity : identityError identity = 0 := by
  have h : (ContinuousMap.restrict (Icc (0:ℝ) 1) (0 : C(ℝ,ℝ))) = 0 := by ext; rfl
  simp [identityError,h]

lemma periodic_iteratedDeriv {f : ℝ → ℝ} {T : ℝ} (hf : Function.Periodic f T) (k : ℕ) :
    Function.Periodic (iteratedDeriv k f) T := by
  induction k with
  | zero => simpa using hf
  | succ k ih => rw [iteratedDeriv_succ]; exact RealCircleCalculus.periodic_deriv ih

lemma jet_difference_periodic (φ ψ : SmoothLift) (k : ℕ) :
    Function.Periodic (fun x => jet φ k x-jet ψ k x) 1 := by
  have hp : Function.Periodic (fun x => φ x-ψ x) 1 := by
    intro x
    change φ (x+1)-ψ (x+1)=φ x-ψ x
    rw [φ.add_one,ψ.add_one]
    ring
  have he : (fun x => jet φ k x-jet ψ k x) = iteratedDeriv k (fun x => φ x-ψ x) := by
    funext x
    exact (iteratedDeriv_sub (φ.smooth.of_le (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))).contDiffAt
      (ψ.smooth.of_le (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))).contDiffAt).symm
  rw [he]
  exact periodic_iteratedDeriv hp k

lemma periodic_bound_from_unitInterval {f : ℝ → ℝ}
    (hf : Function.Periodic f 1) {C : ℝ} (hC : ∀ x ∈ Icc (0:ℝ) 1, |f x| ≤ C) (x : ℝ) :
    |f x| ≤ C := by
  have hx : x-(⌊x⌋ : ℤ) ∈ Icc (0:ℝ) 1 := by
    constructor
    · exact sub_nonneg.mpr (Int.floor_le x)
    · linarith [Int.lt_floor_add_one x]
  have he : f (x-(⌊x⌋ : ℤ))=f x := by simpa using hf.sub_int_mul_eq (x := x) ⌊x⌋
  rw [← he]
  exact hC _ hx

lemma jet_sub_identity_le (φ : SmoothLift) {k : ℕ} (hk : k < 5) (x : ℝ) :
    |jet φ k x-jet identity k x| ≤ identityError φ := by
  apply periodic_bound_from_unitInterval (φ.jet_difference_periodic identity k) _ x
  intro y hy
  have h := ContinuousMap.norm_coe_le_norm
    ((jet φ k-jet identity k).restrict (Icc (0:ℝ) 1)) ⟨y,hy⟩
  apply h.trans
  exact Finset.single_le_sum (f := fun j => ‖(jet φ j-jet identity j).restrict (Icc (0:ℝ) 1)‖)
    (fun j _ => norm_nonneg _)
    (Finset.mem_range.mpr hk)

lemma identityError_controls_zero (φ : SmoothLift) (x : ℝ) : |φ x-x| ≤ identityError φ := by
  simpa [jet] using φ.jet_sub_identity_le (k := 0) (by norm_num) x
lemma identityError_controls_one (φ : SmoothLift) (x : ℝ) : |deriv φ x-1| ≤ identityError φ := by
  simpa [jet,identity] using φ.jet_sub_identity_le (k := 1) (by norm_num) x
lemma identityError_controls_higher (φ : SmoothLift) (k : ℕ) (hk : k ∈ Finset.Icc 2 4) (x : ℝ) :
    |iteratedDeriv k φ x| ≤ identityError φ := by
  have h2 := (Finset.mem_Icc.mp hk).1
  have h4 := (Finset.mem_Icc.mp hk).2
  simpa [jet,identity,iteratedDeriv_id,show k ≠ 0 by omega,show k ≠ 1 by omega]
    using φ.jet_sub_identity_le (k := k) (by omega) x
end StronglyRationalVOA.PositiveCircleGeometry.SmoothLift

namespace StronglyRationalVOA.SmoothCircleLift

def jet (F : SmoothCircleLift) (k : ℕ) : C(ℝ,ℝ) :=
  ⟨iteratedDeriv k F, F.smooth.continuous_iteratedDeriv k
    (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))⟩

 
instance : TopologicalSpace SmoothCircleLift :=
  TopologicalSpace.induced (fun F => jet F) inferInstance

lemma continuous_jet (k : ℕ) : Continuous (fun F : SmoothCircleLift => jet F k) :=
  (continuous_apply k).comp (show Continuous (fun F : SmoothCircleLift => jet F) from continuous_induced_dom)

lemma unitLift_jet (F : SmoothCircleLift) (k : ℕ) :
    PositiveCircleGeometry.SmoothLift.jet F.unitLift k =
      ContinuousMap.const ℝ ((2*Real.pi)⁻¹*(2*Real.pi)^k) *
        (jet F k).comp ⟨fun x => (2*Real.pi)*x, by fun_prop⟩ := by
  ext x
  change iteratedDeriv k (fun y => F (2*Real.pi*y)/(2*Real.pi)) x = _
  simp_rw [div_eq_mul_inv, mul_comm _ (2*Real.pi)⁻¹]
  rw [iteratedDeriv_const_mul_field,
    iteratedDeriv_comp_const_mul (F.smooth.of_le (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤)))]
  change (2*Real.pi)⁻¹*((2*Real.pi)^k*iteratedDeriv k F (2*Real.pi*x)) =
    ((2*Real.pi)⁻¹*(2*Real.pi)^k)*iteratedDeriv k F (2*Real.pi*x)
  ring

lemma continuous_unitLift : Continuous (fun F : SmoothCircleLift => F.unitLift) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro k
  simp only [Function.comp_apply,unitLift_jet]
  exact continuous_const.mul ((ContinuousMap.continuous_precomp _).comp (continuous_jet k))

@[simp] lemma unitLift_one : (1 : SmoothCircleLift).unitLift = PositiveCircleGeometry.SmoothLift.identity := by
  cases h : (1 : SmoothCircleLift).unitLift with
  | mk f hp hs hd =>
    have hf : f=id := by
      funext x
      have hh := congrArg (fun φ : PositiveCircleGeometry.SmoothLift => φ x) h
      simpa using hh.symm
    subst f
    rfl

lemma jet_mul (F G : SmoothCircleLift) (k : ℕ) :
    jet (F*G) k = ∑ c : OrderedFinpartition k,
      (jet F c.length).comp (jet G 0) * ∏ j, jet G (c.partSize j) := by
  ext x
  change iteratedDeriv k (F ∘ G) x = _
  rw [iteratedDeriv_comp_eq_sum_orderedFinpartition F.smooth.contDiffAt G.smooth.contDiffAt
    (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))]
  simp [jet]

 

lemma continuous_mul_right (G : SmoothCircleLift) : Continuous (fun F : SmoothCircleLift => F*G) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro k
  simp only [Function.comp_apply,jet_mul]
  apply continuous_finsetSum
  intro c _
  exact ((ContinuousMap.continuous_precomp _).comp (continuous_jet c.length)).mul continuous_const
end StronglyRationalVOA.SmoothCircleLift

end

end OAI
