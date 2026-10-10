import Mathlib
import OAI.RepresentationTheory.Young.Classification

namespace OAI

/- Finite Young-corner construction. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace CoordinateSweeps.YoungCorner
variable {A : Type*} [Ring A] [Algebra ℂ A]
def sumRow (μ : YoungDiagram) (ρ : Equiv.Perm (Boxes μ) →* A) : A :=
  ∑ r : rows μ, ρ r

def sumCol (μ : YoungDiagram) (ρ : Equiv.Perm (Boxes μ) →* A) : A :=
  ∑ c : cols μ, signScalar (c : Equiv.Perm (Boxes μ)) • ρ c

omit [Algebra ℂ A] in
lemma sumRow_right (μ : YoungDiagram) (ρ : Equiv.Perm (Boxes μ) →* A)
    (r : rows μ) : sumRow μ ρ * ρ r = sumRow μ ρ := by
  rw [sumRow,Finset.sum_mul]
  simp_rw [← map_mul]
  exact Fintype.sum_equiv (Equiv.mulRight r) _ _ (fun _ => rfl)

lemma sumCol_left (μ : YoungDiagram) (ρ : Equiv.Perm (Boxes μ) →* A)
    (c : cols μ) : ρ c * sumCol μ ρ = (signScalar (c : Equiv.Perm (Boxes μ)))⁻¹ • sumCol μ ρ := by
  rw [sumCol,Finset.mul_sum,Finset.smul_sum]
  have hc : signScalar (c : Equiv.Perm (Boxes μ)) ≠ 0 := by
    intro hzero
    have hh : signScalar (c : Equiv.Perm (Boxes μ))*signScalar (c : Equiv.Perm (Boxes μ))⁻¹=1 := by
      rw [← map_mul,mul_inv_cancel,map_one]
    rw [hzero,zero_mul] at hh
    exact zero_ne_one hh
  apply Fintype.sum_equiv (Equiv.mulLeft c)
  intro d
  change ρ (c : Equiv.Perm (Boxes μ)) * (signScalar (d : Equiv.Perm (Boxes μ)) • ρ (d : Equiv.Perm (Boxes μ))) =
    (signScalar (c : Equiv.Perm (Boxes μ)))⁻¹ • (signScalar ((c : Equiv.Perm (Boxes μ)) * (d : Equiv.Perm (Boxes μ))) • ρ ((c : Equiv.Perm (Boxes μ)) * (d : Equiv.Perm (Boxes μ))))
  rw [mul_smul_comm,smul_smul,map_mul,map_mul,← mul_assoc,inv_mul_cancel₀ hc,one_mul]

lemma swap_mem_rows (μ : YoungDiagram) (x y : Boxes μ) (h : x.val.1=y.val.1) :
    Equiv.swap x y ∈ rows μ := by
  intro z
  by_cases hx : z=x
  · subst z; simpa using h.symm
  by_cases hy : z=y
  · subst z; simpa using h
  simp [Equiv.swap_apply_of_ne_of_ne hx hy]

lemma swap_mem_cols (μ : YoungDiagram) (x y : Boxes μ) (h : x.val.2=y.val.2) :
    Equiv.swap x y ∈ cols μ := by
  intro z
  by_cases hx : z=x
  · subst z; simpa using h.symm
  by_cases hy : z=y
  · subst z; simpa using h
  simp [Equiv.swap_apply_of_ne_of_ne hx hy]

/- Transposition cancellation in a Young row/column corner. -/
lemma corner_zero_of_collision (μ : YoungDiagram) (ρ : Equiv.Perm (Boxes μ) →* A)
    (σ : Equiv.Perm (Boxes μ)) (x y : Boxes μ) (hxy : x ≠ y)
    (hrow : x.val.1=y.val.1) (hcol : (σ⁻¹ x).val.2=(σ⁻¹ y).val.2) :
    sumRow μ ρ * ρ σ * sumCol μ ρ=0 := by
  let r : rows μ := ⟨Equiv.swap x y,swap_mem_rows μ x y hrow⟩
  let c : cols μ := ⟨Equiv.swap (σ⁻¹ x) (σ⁻¹ y),swap_mem_cols μ _ _ hcol⟩
  have hcxy : σ⁻¹ x ≠ σ⁻¹ y := fun h => hxy ((σ⁻¹).injective h)
  have he : (r : Equiv.Perm (Boxes μ))*σ = σ*(c : Equiv.Perm (Boxes μ)) := by
    apply Equiv.ext
    intro z
    change Equiv.swap x y (σ z) = σ (Equiv.swap (σ⁻¹ x) (σ⁻¹ y) z)
    by_cases hx : z=σ⁻¹ x
    · subst z; simp
    by_cases hy : z=σ⁻¹ y
    · subst z; simp
    have hx' : σ z ≠ x := by
      intro he; apply hx
      have hh := congrArg (fun a => σ⁻¹ a) he
      simpa using hh
    have hy' : σ z ≠ y := by
      intro he; apply hy
      have hh := congrArg (fun a => σ⁻¹ a) he
      simpa using hh
    rw [Equiv.swap_apply_of_ne_of_ne hx hy,Equiv.swap_apply_of_ne_of_ne hx' hy']
  have hc : (signScalar (c : Equiv.Perm (Boxes μ)))⁻¹ = -1 := by rw [show (c : Equiv.Perm (Boxes μ))=Equiv.swap (σ⁻¹ x) (σ⁻¹ y) from rfl,signScalar_swap _ _ hcxy]; norm_num
  have hh : sumRow μ ρ * ρ σ * sumCol μ ρ = -(sumRow μ ρ * ρ σ * sumCol μ ρ) := by
    calc
      _ = (sumRow μ ρ * ρ r)*ρ σ*sumCol μ ρ := by rw [sumRow_right]
      _ = sumRow μ ρ * (ρ σ * ρ c) * sumCol μ ρ := by rw [mul_assoc (sumRow μ ρ) (ρ r) (ρ σ),← map_mul,he,map_mul]
      _ = sumRow μ ρ * ρ σ * (ρ c * sumCol μ ρ) := by simp only [mul_assoc]
      _ = _ := by rw [sumCol_left,hc]; simp
  have htwo : (2 : ℂ) • (sumRow μ ρ * ρ σ * sumCol μ ρ)=0 := by
    rw [two_smul,← eq_neg_iff_add_eq_zero]
    exact hh
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

/- The one-dimensional Young corner in every complex matrix representation,
proved by Ferrers sorting. -/
theorem corner_scalar (μ : YoungDiagram) (ρ : Equiv.Perm (Boxes μ) →* A)
    (σ : Equiv.Perm (Boxes μ)) :
    ∃ c : ℂ, sumRow μ ρ * ρ σ * sumCol μ ρ = c • (sumRow μ ρ * sumCol μ ρ) := by
  by_cases h : NoCollision μ σ⁻¹
  · obtain ⟨c,hc,r,hr,he⟩ := factor_column_row μ σ⁻¹ h
    have hi : σ = r⁻¹*c⁻¹ := by rw [← mul_inv_rev,← he,inv_inv]
    refine ⟨(signScalar c⁻¹)⁻¹,?_⟩
    rw [hi,map_mul,← mul_assoc,sumRow_right μ ρ ⟨r⁻¹,(rows μ).inv_mem hr⟩,
      mul_assoc,sumCol_left μ ρ ⟨c⁻¹,(cols μ).inv_mem hc⟩,mul_smul_comm]
  · simp only [NoCollision] at h
    push Not at h
    obtain ⟨x,y,hrow,hcol,hxy⟩ := h
    exact ⟨0,by rw [corner_zero_of_collision μ ρ σ x y hxy hrow hcol,zero_smul]⟩

end CoordinateSweeps.YoungCorner

namespace CoordinateSweeps.RepDetection
variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]

def orbitSpan (τ : Representation ℂ G V) (v : V) : Subrepresentation τ where
  toSubmodule := Submodule.span ℂ (Set.range (fun g => τ g v))
  apply_mem_toSubmodule := by
    intro g w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨k,rfl⟩ := hw
      apply Submodule.subset_span
      exact ⟨g*k,by simp only [map_mul,Module.End.mul_apply]⟩
    | zero => simp
    | add x y hx hy ix iy => simpa using Submodule.add_mem _ ix iy
    | smul c x hx ix => simpa using Submodule.smul_mem _ c ix

lemma mem_orbitSpan (τ : Representation ℂ G V) (v : V) : v ∈ orbitSpan τ v := by
  apply Submodule.subset_span
  exact ⟨1,by simp⟩

lemma orbitSpan_le (τ : Representation ℂ G V) (v : V) (S : Subrepresentation τ) (hv : v∈S) :
    orbitSpan τ v≤S := by
  apply Submodule.span_le.mpr
  rintro w ⟨g,rfl⟩
  exact S.apply_mem_toSubmodule g hv

end CoordinateSweeps.RepDetection

namespace CoordinateSweeps.YoungCorner

def unitVector (μ : YoungDiagram) : Equiv.Perm (Boxes μ) → ℂ := fun g => if g=1 then 1 else 0

def columnGenerator (μ : YoungDiagram) := sumCol μ (regular (Equiv.Perm (Boxes μ))) (unitVector μ)
def youngVector (μ : YoungDiagram) := sumRow μ (regular (Equiv.Perm (Boxes μ))) (columnGenerator μ)
abbrev columnModule (μ : YoungDiagram) := RepDetection.orbitSpan (regular (Equiv.Perm (Boxes μ))) (columnGenerator μ)

lemma youngVector_one (μ : YoungDiagram) : youngVector μ 1=1 := by
  have hv : (fixedSum (rowColor (Equiv.refl (Boxes μ))) (regular (Equiv.Perm (Boxes μ))) *
      alternatingSum (colColor (Equiv.refl (Boxes μ))) (regular (Equiv.Perm (Boxes μ)))) (unitVector μ) 1=1 := by
    simp only [fixedSum,alternatingSum,Module.End.mul_apply,LinearMap.sum_apply,regular_apply,
      Finset.sum_apply,LinearMap.smul_apply,Pi.smul_apply,smul_eq_mul,mul_one,unitVector,
      ← mul_inv_rev,inv_eq_one,row_column_intersection]
    simp [ite_and]
  exact hv

lemma youngVector_ne_zero (μ : YoungDiagram) : youngVector μ ≠ 0 := by
  intro h
  have hh:=youngVector_one μ
  rw [h] at hh
  exact zero_ne_one hh

lemma youngVector_mem (μ : YoungDiagram) : youngVector μ ∈ columnModule μ := by
  change (sumRow μ (regular (Equiv.Perm (Boxes μ)))) (columnGenerator μ) ∈ (columnModule μ).toSubmodule
  simp only [sumRow,LinearMap.sum_apply]
  apply Submodule.sum_mem
  intro r hr
  exact (columnModule μ).apply_mem_toSubmodule r (RepDetection.mem_orbitSpan _ _)

lemma sumRow_square (μ : YoungDiagram) {A : Type*} [Ring A] [Algebra ℂ A]
    (ρ : Equiv.Perm (Boxes μ) →* A) :
    sumRow μ ρ * sumRow μ ρ=(Fintype.card (rows μ) : ℂ) • sumRow μ ρ := by
  conv_lhs => rhs; rw [sumRow]
  rw [Finset.mul_sum]
  simp only [sumRow_right,Finset.sum_const,Finset.card_univ]
  exact (Nat.cast_smul_eq_nsmul ℂ _ _).symm

lemma sumRow_youngVector (μ : YoungDiagram) :
    sumRow μ (regular (Equiv.Perm (Boxes μ))) (youngVector μ)=
      (Fintype.card (rows μ) : ℂ) • youngVector μ := by
  have hh:=congrArg (fun A : Module.End ℂ (Equiv.Perm (Boxes μ) → ℂ) => A (columnGenerator μ))
    (sumRow_square μ (regular (Equiv.Perm (Boxes μ))))
  exact hh

lemma rowImage_line (μ : YoungDiagram) (v : columnModule μ) :
    sumRow μ (regular (Equiv.Perm (Boxes μ))) (v : Equiv.Perm (Boxes μ) → ℂ) ∈
      Submodule.span ℂ {youngVector μ} := by
  suffices hh : ∀ w ∈ (columnModule μ).toSubmodule, sumRow μ (regular (Equiv.Perm (Boxes μ))) w ∈
    Submodule.span ℂ {youngVector μ} from hh v v.property
  intro w hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨g,rfl⟩ := hw
    obtain ⟨c,hc⟩ := corner_scalar μ (regular (Equiv.Perm (Boxes μ))) g
    have hh:=congrArg (fun A : Module.End ℂ (Equiv.Perm (Boxes μ) → ℂ) => A (unitVector μ)) hc
    change sumRow μ (regular (Equiv.Perm (Boxes μ)))
      (regular (Equiv.Perm (Boxes μ)) g (columnGenerator μ))=c • youngVector μ at hh
    rw [hh]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  | zero => simp
  | add x y hx hy ix iy => simpa using Submodule.add_mem _ ix iy
  | smul c x hx ix => simpa using Submodule.smul_mem _ c ix

end CoordinateSweeps.YoungCorner

namespace CoordinateSweeps.YoungCorner

lemma col_row_col_eq_one (μ : YoungDiagram) (c d : cols μ) (r : rows μ) :
    (c.val*r.val)*d.val=1 ↔ r=1 ∧ d=c⁻¹ := by
  constructor
  · intro h
    have he : r.val*(d*c).val=1 := by
      calc
        _ = c.val⁻¹*(c.val*r.val*d.val)*c.val := by simp [mul_assoc]
        _ = _ := by rw [h]; simp
    obtain ⟨hr,hd⟩ := (row_column_intersection μ (Equiv.refl _) r (d*c)).mp he
    exact ⟨hr,mul_eq_one_iff_eq_inv.mp hd⟩
  · rintro ⟨rfl,rfl⟩
    simp

lemma col_youngVector_one (μ : YoungDiagram) :
    sumCol μ (regular (Equiv.Perm (Boxes μ))) (youngVector μ) 1=(Fintype.card (cols μ) : ℂ) := by
  simp only [youngVector,columnGenerator,sumRow,sumCol,LinearMap.sum_apply,
    LinearMap.smul_apply,Pi.smul_apply,regular_apply,Finset.sum_apply,smul_eq_mul,
    Finset.mul_sum,mul_one,unitVector]
  simp_rw [← mul_inv_rev,inv_eq_one,col_row_col_eq_one]
  simp only [ite_and]
  have hn (c : cols μ) : signScalar c.val ≠ 0 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign c.val) with h|h <;> simp [signScalar,h]
  simp [mul_inv_cancel₀ (hn _)]

lemma col_youngVector_ne_zero (μ : YoungDiagram) :
    sumCol μ (regular (Equiv.Perm (Boxes μ))) (youngVector μ) ≠ 0 := by
  intro h
  have he := col_youngVector_one μ
  rw [h] at he
  have hc : (Fintype.card (cols μ) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  exact hc he.symm

end CoordinateSweeps.YoungCorner

namespace CoordinateSweeps.YoungCorner

lemma spechtSeed_exists (μ : YoungDiagram) :
    ∃ S : Subrepresentation (columnModule μ).toRepresentation,
      S.toRepresentation.IsIrreducible ∧ hasShape μ (Equiv.refl _) S.toRepresentation ∧
      ∃ v : S.toSubmodule, ((v : (columnModule μ).toSubmodule) : Equiv.Perm (Boxes μ) → ℂ)=youngVector μ := by
  let T := columnModule μ
  let : AddCommGroup T.toSubmodule := inferInstance
  let P : Module.End ℂ T.toSubmodule := sumRow μ T.toRepresentation
  have hP : P ≠ 0 := by
    intro hz
    have hh:=congrArg (fun A : Module.End ℂ T.toSubmodule =>
      (A ⟨youngVector μ,youngVector_mem μ⟩ : Equiv.Perm (Boxes μ) → ℂ)) hz
    change (fixedSum (A := Module.End ℂ T.toSubmodule) (rowColor (Equiv.refl (Boxes μ))) T.toRepresentation ⟨youngVector μ,youngVector_mem μ⟩ : Equiv.Perm (Boxes μ) → ℂ)=0 at hh
    rw [fixedSum_subrepresentation] at hh
    change sumRow μ (regular (Equiv.Perm (Boxes μ))) (youngVector μ)=0 at hh
    rw [sumRow_youngVector] at hh
    have hc : (Fintype.card (rows μ) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    exact youngVector_ne_zero μ ((smul_eq_zero.mp hh).resolve_left hc)
  obtain ⟨S,hS,v,hv⟩:=RepDetection.exists_irreducible_detecting T.toRepresentation P hP
  let : AddCommGroup S.toSubmodule := inferInstance
  have hPmap (w : S.toSubmodule) :
      (((sumRow (A := Module.End ℂ S.toSubmodule) μ S.toRepresentation w : S.toSubmodule) : T.toSubmodule) : Equiv.Perm (Boxes μ) → ℂ)=
        sumRow μ (regular (Equiv.Perm (Boxes μ))) ((w : T.toSubmodule) : Equiv.Perm (Boxes μ) → ℂ) := by
    change ((fixedSum (A := Module.End ℂ S.toSubmodule) (rowColor (Equiv.refl (Boxes μ))) S.toRepresentation w : T.toSubmodule) : Equiv.Perm (Boxes μ) → ℂ)=_
    rw [fixedSum_subrepresentation,fixedSum_subrepresentation]
    rfl
  have hQmap (w : S.toSubmodule) :
      (((sumCol (A := Module.End ℂ S.toSubmodule) μ S.toRepresentation w : S.toSubmodule) : T.toSubmodule) : Equiv.Perm (Boxes μ) → ℂ)=
        sumCol μ (regular (Equiv.Perm (Boxes μ))) ((w : T.toSubmodule) : Equiv.Perm (Boxes μ) → ℂ) := by
    change ((alternatingSum (A := Module.End ℂ S.toSubmodule) (colColor (Equiv.refl (Boxes μ))) S.toRepresentation w : T.toSubmodule) : Equiv.Perm (Boxes μ) → ℂ)=_
    rw [alternatingSum_subrepresentation,alternatingSum_subrepresentation]
    rfl
  have hPv : (P (v : T.toSubmodule) : Equiv.Perm (Boxes μ) → ℂ)=
      sumRow μ (regular (Equiv.Perm (Boxes μ))) ((v : T.toSubmodule) : Equiv.Perm (Boxes μ) → ℂ) :=
    fixedSum_subrepresentation (rowColor (Equiv.refl (Boxes μ))) (regular (Equiv.Perm (Boxes μ))) T v
  obtain ⟨c,hc⟩:=Submodule.mem_span_singleton.mp (rowImage_line μ (v : T.toSubmodule))
  have hcn : c ≠ 0 := by
    intro hz
    rw [hz,zero_smul] at hc
    apply hv
    apply Subtype.ext
    rw [hPv]
    exact hc.symm
  let w : S.toSubmodule := c⁻¹ • sumRow (A := Module.End ℂ S.toSubmodule) μ S.toRepresentation v
  have hw : ((w : T.toSubmodule) : Equiv.Perm (Boxes μ) → ℂ)=youngVector μ := by
    change c⁻¹ • (((sumRow (A := Module.End ℂ S.toSubmodule) μ S.toRepresentation v : S.toSubmodule) : T.toSubmodule) : Equiv.Perm (Boxes μ) → ℂ)=_
    rw [hPmap,← hc,smul_smul,inv_mul_cancel₀ hcn,one_smul]
  have hPS : sumRow (A := Module.End ℂ S.toSubmodule) μ S.toRepresentation ≠ 0 := by
    intro hz
    have hh:=hPmap v
    rw [hz] at hh
    apply hv
    apply Subtype.ext
    rw [hPv]
    exact hh.symm
  have hQS : sumCol (A := Module.End ℂ S.toSubmodule) μ S.toRepresentation ≠ 0 := by
    intro hz
    have hh:=hQmap w
    rw [hz,hw] at hh
    exact col_youngVector_ne_zero μ hh.symm
  let :=hS
  have hSh : hasShape μ (Equiv.refl _) S.toRepresentation := by
    obtain ⟨g,hg⟩:=RepDetection.exists_cross_nonzero S.toRepresentation _ _ hPS hQS
    obtain ⟨a,ha⟩:=corner_scalar μ S.toRepresentation g
    intro hz
    apply hg
    change sumRow (A := Module.End ℂ S.toSubmodule) μ S.toRepresentation * sumCol (A := Module.End ℂ S.toSubmodule) μ S.toRepresentation=0 at hz
    rw [ha,hz,smul_zero]
  exact ⟨S,hS,hSh,w,hw⟩

end CoordinateSweeps.YoungCorner

namespace CoordinateSweeps.YoungCorner
/- A rank-preserving row-times-column factor has to be the identity.
This gives independent Young vectors for the entire rank stabilizer. -/
lemma rank_row_col (μ : YoungDiagram) (r : rows μ) (c : cols μ)
    (h : ∀ x : Boxes μ, ((r.val*c.val) x).val.1+((r.val*c.val) x).val.2=x.val.1+x.val.2) :
    r=1 ∧ c=1 := by
  let i : Boxes μ → ℝ := fun x => x.val.1
  let j : Boxes μ → ℝ := fun x => x.val.2
  have hr (x : Boxes μ) : i (r.val x)=i x := congrArg (fun m : ℕ => (m : ℝ)) (r.property x)
  have hc (x : Boxes μ) : j (c.val x)=j x := congrArg (fun m : ℕ => (m : ℝ)) (c.property x)
  have hh (x : Boxes μ) : i (c.val x)+j ((r.val*c.val) x)=i x+j x := by
    have hx:=congrArg (fun m : ℕ => (m : ℝ)) (h x)
    simp only [Nat.cast_add] at hx
    change i (r.val (c.val x))+j ((r.val*c.val) x)=i x+j x at hx
    simpa only [hr] using hx
  have hi : ∑ x, i (c.val x)^2=∑ x, i x^2 :=
    Fintype.sum_equiv c.val _ _ (fun _ => rfl)
  have hij₁ : ∑ x, i (c.val x)*j x=∑ x, i x*j x := by
    simpa only [hc] using (Fintype.sum_equiv c.val (fun x => i (c.val x)*j (c.val x)) (fun x => i x*j x) (fun _ => rfl))
  have hij₂ : ∑ x, i (c.val x)*j ((r.val*c.val) x)=∑ x, i x*j x := by
    simpa only [Equiv.Perm.mul_apply,hr] using
      (Fintype.sum_equiv (r.val*c.val) (fun x => i ((r.val*c.val) x)*j ((r.val*c.val) x)) (fun x => i x*j x) (fun _ => rfl))
  have hprod : ∑ x, i (c.val x)*i x=∑ x, i x^2 := by
    have he : ∑ x, (i (c.val x)*i x + i (c.val x)*j x)=
        ∑ x, (i (c.val x)^2+i (c.val x)*j ((r.val*c.val) x)) := by
      apply Finset.sum_congr rfl
      intro x hx
      have ht := congrArg (fun z : ℝ => i (c.val x)*z) (hh x)
      nlinarith only [ht]
    simp only [Finset.sum_add_distrib,hi,hij₁,hij₂] at he
    linarith
  have hz : ∑ x, (i (c.val x)-i x)^2=0 := by
    have he : ∑ x, (i (c.val x)-i x)^2=
        (∑ x, i (c.val x)^2)+(∑ x, i x^2)-2*(∑ x, i (c.val x)*i x) := by
      simp only [← Finset.sum_add_distrib,← Finset.sum_sub_distrib,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    rw [he,hi,hprod]
    ring
  have hci (x : Boxes μ) : i (c.val x)=i x := by
    have he := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => sq_nonneg (i (c.val x)-i x))).mp hz x (Finset.mem_univ x)
    nlinarith [sq_nonneg (i (c.val x)-i x)]
  have ce : c=1 := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    apply Subtype.ext
    apply Prod.ext
    · have hx :=hci x
      dsimp [i] at hx
      exact_mod_cast hx
    · exact c.property x
  subst c
  refine ⟨?_,rfl⟩
  apply Subtype.ext
  apply Equiv.ext
  intro x
  apply Subtype.ext
  apply Prod.ext
  · exact r.property x
  · have hx:=h x
    have hr:=r.property x
    simpa only [Subgroup.coe_one,mul_one,Equiv.Perm.one_apply,hr,Nat.add_left_cancel_iff] using hx

end CoordinateSweeps.YoungCorner

namespace CoordinateSweeps.YoungCorner

lemma card_perm_le_colors_mul_stabilizer {X Y : Type*} [Fintype X] [DecidableEq X]
    [Fintype Y] (f : X → Y) :
    (Fintype.card X).factorial ≤ (Fintype.card Y)^(Fintype.card X) * Fintype.card (colorStabilizer f) := by
  let A (g : Equiv.Perm X) : X → Y := fun x => f (g x)
  let rep (y : X → Y) : Equiv.Perm X := if h : ∃ g, A g=y then h.choose else 1
  have hrep (g : Equiv.Perm X) : A (rep (A g))=A g := by
    simp only [rep,dite_eq_left (show ∃ t, A t=A g from ⟨g,rfl⟩)]
    exact Exists.choose_spec (show ∃ t, A t=A g from ⟨g,rfl⟩)
  let enc (g : Equiv.Perm X) : (X → Y) × colorStabilizer f :=
    (A g,⟨g*(rep (A g))⁻¹,by
      intro x
      have hx:=congrFun (hrep g) ((rep (A g))⁻¹ x)
      simpa [A] using hx.symm⟩)
  have hi : Function.Injective enc := by
    intro g h he
    have hA : A g=A h := congrArg Prod.fst he
    have hk : g*(rep (A g))⁻¹=h*(rep (A h))⁻¹ := congrArg (fun z => z.2.val) he
    rw [hA] at hk
    exact mul_right_cancel hk
  have hc:=Fintype.card_le_of_injective enc hi
  simpa only [Fintype.card_perm,Fintype.card_prod,Fintype.card_fun] using hc

end CoordinateSweeps.YoungCorner

namespace CoordinateSweeps.YoungCorner

def ranks (μ : YoungDiagram) : Subgroup (Equiv.Perm (Boxes μ)) :=
  colorStabilizer (fun x => x.val.1+x.val.2)

lemma youngVector_rank_value (μ : YoungDiagram) (g : ranks μ) :
    youngVector μ g.val = if g.val=1 then 1 else 0 := by
  have he (r : rows μ) (c : cols μ) :
      c.val⁻¹*(r.val⁻¹*g.val)=1 ↔ r=1 ∧ c=1 ∧ g.val=1 := by
    constructor
    · intro h
      have hg : g.val=r.val*c.val := by
        calc
          _ = (r.val*c.val)*(c.val⁻¹*(r.val⁻¹*g.val)) := by group
          _ = _ := by rw [h,mul_one]
      obtain ⟨hr,hc⟩:=rank_row_col μ r c (by intro x; rw [← hg]; exact g.property x)
      exact ⟨hr,hc,by simpa [hr,hc] using hg⟩
    · rintro ⟨rfl,rfl,hg⟩
      simp [hg]
  simp only [youngVector,columnGenerator,sumRow,sumCol,LinearMap.sum_apply,
    LinearMap.smul_apply,Pi.smul_apply,regular_apply,Finset.sum_apply,smul_eq_mul,
    unitVector,he]
  simp [ite_and]

lemma rankVectors_eval (μ : YoungDiagram) (u t : ranks μ) :
    regular (Equiv.Perm (Boxes μ)) u.val (youngVector μ) t.val=if u=t then 1 else 0 := by
  change youngVector μ ((u⁻¹*t).val)=_
  rw [youngVector_rank_value]
  simp only [Subgroup.coe_mul,Subgroup.coe_inv,inv_mul_eq_one,Subtype.val_inj]

lemma rankVectors_independent (μ : YoungDiagram) :
    LinearIndependent ℂ (fun u : ranks μ => regular (Equiv.Perm (Boxes μ)) u.val (youngVector μ)) := by
  apply linearIndependent_iff'.mpr
  intro s a he t ht
  have hh:=congrFun he t.val
  simp only [Finset.sum_apply,Pi.smul_apply,rankVectors_eval,Pi.zero_apply,smul_eq_mul] at hh
  simpa [mul_ite,Finset.sum_ite_eq',ht] using hh

lemma rank_card_le_shape_finrank (μ : YoungDiagram) {V : Type} [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] (τ : Representation ℂ (Equiv.Perm (Boxes μ)) V)
    [τ.IsIrreducible] (hτ : hasShape μ (Equiv.refl _) τ) :
    Fintype.card (ranks μ) ≤ Module.finrank ℂ V := by
  obtain ⟨S,hS,hShape,v,hv⟩:=spechtSeed_exists μ
  let:=hS
  let : AddCommGroup (columnModule μ).toSubmodule := inferInstance
  let : AddCommGroup S.toSubmodule := inferInstance
  obtain ⟨e⟩:=equiv_of_same_shape τ S.toRepresentation μ (Equiv.refl _) (Equiv.refl _) hτ hShape
  rw [e.toLinearEquiv.finrank_eq]
  let f (g : ranks μ) : S.toSubmodule := S.toRepresentation g.val v
  have hmap (g : ranks μ) : ((f g : (columnModule μ).toSubmodule) : Equiv.Perm (Boxes μ) → ℂ)=
      regular (Equiv.Perm (Boxes μ)) g.val (youngVector μ) := by
    change regular (Equiv.Perm (Boxes μ)) g.val ((v : (columnModule μ).toSubmodule) : Equiv.Perm (Boxes μ) → ℂ)=_
    rw [hv]
  let L : S.toSubmodule →ₗ[ℂ] (Equiv.Perm (Boxes μ) → ℂ) :=
    (columnModule μ).toSubmodule.subtype.comp S.toSubmodule.subtype
  have hli : LinearIndependent ℂ f := by
    apply LinearIndependent.of_comp L
    change LinearIndependent ℂ (fun g => ((f g : (columnModule μ).toSubmodule) : Equiv.Perm (Boxes μ) → ℂ))
    simpa only [hmap] using rankVectors_independent μ
  exact hli.fintype_card_le_finrank

/- Entropy lower bound from Young vectors for the removed-diagram step of the
main induction. -/
lemma shape_dimension_entropy (μ : YoungDiagram) {V : Type} [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] (τ : Representation ℂ (Equiv.Perm (Boxes μ)) V)
    [τ.IsIrreducible] (hτ : hasShape μ (Equiv.refl _) τ)
    (L : ℕ) (hL : ∀ x : Boxes μ, x.val.1+x.val.2<L) :
    (Fintype.card (Boxes μ)).factorial ≤ L^(Fintype.card (Boxes μ))*Module.finrank ℂ V := by
  let f (x : Boxes μ) : Fin L := ⟨x.val.1+x.val.2,hL x⟩
  have he : colorStabilizer f=ranks μ := by
    ext g
    constructor
    · intro h x
      exact congrArg Fin.val (h x)
    · intro h x
      exact Fin.ext (h x)
  have hc:=card_perm_le_colors_mul_stabilizer f
  rw [he,Fintype.card_fin] at hc
  exact hc.trans (Nat.mul_le_mul_left _ (rank_card_le_shape_finrank μ τ hτ))

end CoordinateSweeps.YoungCorner
end

open scoped Matrix.Norms.L2Operator

end OAI
