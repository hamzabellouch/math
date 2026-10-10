import OAI.RingTheory.BassTrace.TwistedPaths

namespace OAI

noncomputable section

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral

namespace BassTrace.PathChains

section

open scoped BigOperators

open Oriented ChainHomotopy Paths Detector

variable {G : Type*} [Group G]

def relations (g : G) (n : ℕ) : Submodule ℂ (Degree (Vertex g) n) :=
  Submodule.span ℂ (Set.range fun p : Subgroup.centralizer ({g} : Set G) ×
    Degree (Vertex g) n => relabel n (centralizerAct g p.1) p.2-p.2)

abbrev Coinvariant (g : G) (n : ℕ) := Degree (Vertex g) n ⧸ relations g n

def quotientMap (g : G) (n : ℕ) : Degree (Vertex g) n →ₗ[ℂ] Coinvariant g n :=
  (relations g n).mkQ

lemma quotientMap_invariant (g : G) (n : ℕ)
    (c : Subgroup.centralizer ({g} : Set G)) (x : Degree (Vertex g) n) :
    quotientMap g n (relabel n (centralizerAct g c) x) = quotientMap g n x := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  exact (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.subset_span ⟨(c,x),rfl⟩)

lemma d_relations (g : G) (n : ℕ) {x : Degree (Vertex g) (n+1)}
    (hx : x ∈ relations g (n+1)) : d n x ∈ relations g n := by
  classical
  let : LinearOrder (Vertex g) := linearOrderOfSTO WellOrderingRel
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨c,y⟩,rfl⟩ := hx
    rw [map_sub,d_relabel]
    exact Submodule.subset_span ⟨(c,d n y),rfl⟩
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  | smul a x _ hx => simpa only [map_smul] using Submodule.smul_mem _ a hx

def quotientD (g : G) (n : ℕ) : Coinvariant g (n+1) →ₗ[ℂ] Coinvariant g n :=
  (relations g (n+1)).liftQ ((quotientMap g n).comp (d n)) (by
    intro x hx
    change quotientMap g n (d n x) = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr (d_relations g n hx))

@[simp] lemma quotientD_mk (g : G) (n : ℕ) (x : Degree (Vertex g) (n+1)) :
    quotientD g n (quotientMap g (n+1) x) = quotientMap g n (d n x) := rfl

def pathProjection (g : G) (n : ℕ) : Orbit g n → Coinvariant g (n+1) :=
  Quotient.lift (fun h => quotientMap g (n+1) (wedge (n+1) (project g ∘ h))) (by
    intro h k hhk
    obtain ⟨c,hc⟩ := hhk
    have he : k = fun i => (c:G)*h i := funext fun i => (hc i).symm
    rw [he]
    simpa only [relabel_wedge, Function.comp_def, centralizerAct_project] using
      (quotientMap_invariant g (n+1) c (wedge (n+1) (project g ∘ h))).symm)

@[simp] lemma pathProjection_mk (g : G) (n : ℕ) (h : Fin (n+1) → G) :
    pathProjection g n (Quotient.mk _ h) =
      quotientMap g (n+1) (wedge (n+1) (project g ∘ h)) := rfl

lemma projected_twist (g : G) (n : ℕ) (h : Fin (n+1) → G) :
    project g ∘ twist g n h = (project g ∘ h) ∘ finRotate (n+1) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Function.comp_apply,twist_last,finRotate_last]
    apply (project_eq_iff g _ _).mpr
    exact ⟨-1,by simp [← mul_assoc]⟩
  · simp only [Function.comp_apply,twist_castSucc,rotate_castSucc]

lemma pathProjection_twist (g : G) (n : ℕ) (q : Orbit g n) :
    pathProjection g n (orbitTwist g n q) = (-1:ℂ)^n • pathProjection g n q := by
  induction q using Quotient.inductionOn with | _ h =>
    change quotientMap g (n+1) (wedge (n+1) (project g ∘ twist g n h)) = _
    rw [projected_twist,wedge_perm]
    simp [sign_finRotate,Units.smul_def,← Int.cast_smul_eq_zsmul ℂ]

variable {ι : Type*} [Fintype ι]

def pathChain (e : GroupMatrix (G := G) (ι := ι)) (g : G) (n : ℕ) :
    Coinvariant g (n+1) :=
  Finsupp.linearCombination ℂ (pathProjection g n) (pathVector e g n)

lemma pathChain_twist (e : GroupMatrix (G := G) (ι := ι)) (g : G) (n : ℕ) :
    pathChain e g n = (-1:ℂ)^n • pathChain e g n := by
  have hv := congrArg (Finsupp.linearCombination ℂ (pathProjection g n))
    (pathVector_twist e g n)
  rw [Finsupp.linearCombination_apply,Finsupp.sum_mapDomain_index] at hv
  swap
  · intro q; simp
  swap
  · intro q a b; exact add_smul a b _
  simp only [pathProjection_twist] at hv
  simp_rw [smul_comm _ ((-1:ℂ)^n)] at hv
  have hh : (pathVector e g n).sum (fun a b =>
      (-1:ℂ)^n • (b • pathProjection g n a)) = (-1:ℂ)^n • pathChain e g n := by
    simp only [pathChain,Finsupp.linearCombination_apply,Finsupp.sum,Finset.smul_sum]
  rw [hh] at hv
  exact hv.symm

lemma pathChain_odd (e : GroupMatrix (G := G) (ι := ι)) (g : G) (m : ℕ) :
    pathChain e g (2*m+1) = 0 := by
  have ht := pathChain_twist e g (2*m+1)
  rw [complex_sign_odd m,neg_one_smul] at ht
  have hz : (2:ℂ) • pathChain e g (2*m+1) = 0 := by
    rw [two_smul]
    exact eq_neg_iff_add_eq_zero.mp ht
  exact (smul_eq_zero.mp hz).resolve_left (by norm_num)

end

open scoped BigOperators

open Oriented ChainHomotopy Paths Detector

variable {G : Type*} [Group G]

lemma pathProjection_boundary (g : G) (n : ℕ) (q : Orbit g (n+1)) :
    quotientD g (n+1) (pathProjection g (n+1) q) =
      ∑ i : Fin (n+2), (-1:ℂ)^i.val • pathProjection g n (deleteEntry g n i q) := by
  induction q using Quotient.inductionOn with | _ h =>
    change quotientMap g (n+1) (d (n+1) (wedge (n+2) (project g ∘ h))) = _
    rw [d_wedge,map_sum]
    simp only [map_smul]
    rfl

variable {ι : Type*} [Fintype ι]

lemma pathChain_boundary (e : GroupMatrix (G := G) (ι := ι)) (he : e*e=e)
    (g : G) (n : ℕ) : quotientD g (n+1) (pathChain e g (n+1)) =
      ∑ i : Fin (n+2), (-1:ℂ)^i.val • pathChain e g n := by
  classical
  unfold pathChain
  rw [LinearMap.map_finsupp_linearCombination]
  simp only [Function.comp_apply,pathProjection_boundary,Finsupp.linearCombination_apply,Finsupp.sum]
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [smul_comm _ ((-1:ℂ)^i.val)]
  have heq : (Finsupp.linearCombination ℂ ((pathProjection g n) ∘ deleteEntry g n i))
      (pathVector e g (n+1)) = (Finsupp.linearCombination ℂ (pathProjection g n))
      (pathVector e g n) := by
    rw [← Finsupp.linearCombination_mapDomain, pathVector_deleteEntry e he]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, Function.comp_apply] at heq
  simpa only [Finset.smul_sum] using congrArg (fun x => (-1:ℂ)^i.val • x) heq

theorem pathChain_even_cycle (e : GroupMatrix (G := G) (ι := ι)) (he : e*e=e)
    (g : G) (m : ℕ) : quotientD g (2*m+2) (pathChain e g (2*(m+1))) = 0 := by
  change quotientD g ((2*m+1)+1) (pathChain e g ((2*m+1)+1)) = 0
  rw [pathChain_boundary e he]
  simp only [pathChain_odd,smul_zero,Finset.sum_const_zero]

variable (g : G) (β : G → G → ℂ)
    (hc : ∀ (c : Subgroup.centralizer ({g} : Set G)) h k, β (c*h) (c*k) = β h k)
    (hl : ∀ (r s : ℤ) h k, β (g^r*h) (g^s*k) = β h k+s-r)

def quotientCocycle (m : ℕ) : Coinvariant g (2*m+1) →ₗ[ℂ] ℂ :=
  (relations g (2*m+1)).liftQ (cosetCocycle g m β) (by
    intro x hx
    change cosetCocycle g m β x = 0
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨c,y⟩,rfl⟩ := hx
      rw [map_sub,cosetCocycle_invariant g m β hc hl,sub_self]
    | zero => exact map_zero _
    | add x y _ _ hx hy => rw [map_add,hx,hy,add_zero]
    | smul a x _ hx => rw [map_smul,hx,smul_zero])

lemma quotientCocycle_pathProjection (m : ℕ) (q : Orbit g (2*m)) :
    quotientCocycle g β hc hl m (pathProjection g (2*m) q) = orbitDetector g β hc m q := by
  induction q using Quotient.inductionOn with | _ h =>
    exact cosetCocycle_lifts g m β hl h

lemma quotientCocycle_pairing (e : GroupMatrix (G := G) (ι := ι)) (he : e*e=e)
    (hβ : ∀ h k, β h k = -β k h) (m : ℕ) :
    quotientCocycle g β hc hl m (pathChain e g (2*m)) =
      (2:ℂ)⁻¹^m*totalWeight e g 0 := by
  unfold pathChain
  rw [LinearMap.map_finsupp_linearCombination]
  simp only [Function.comp_apply,quotientCocycle_pathProjection,Finsupp.linearCombination_apply,smul_eq_mul]
  exact detectorSum_value g β hc e he hβ hl m

lemma quotientCocycle_closed (hβ : ∀ h k, β h k = -β k h) (m : ℕ)
    (x : Coinvariant g (2*m+2)) :
    quotientCocycle g β hc hl m (quotientD g (2*m+1) x) = 0 := by
  induction x using Submodule.Quotient.induction_on with | _ x =>
    exact cosetCocycle_closed g m β hβ x

end BassTrace.PathChains

end

end OAI
