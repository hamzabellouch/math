import OAI.RingTheory.BassTrace.RelativeExponents

namespace OAI

noncomputable section

namespace BassTrace

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral

namespace Detector

open scoped BigOperators

variable {G : Type*} [Group G]

def twistedRotation (g : G) (n : ℕ) (h : Fin (n+1) → G) (i : Fin (n+1)) : G :=
  g ^ (if i = Fin.last n then (1 : ℤ) else 0) * h (finRotate (n+1) i)

lemma finRotate_castSucc {n : ℕ} (i : Fin n) : finRotate (n+1) i.castSucc = i.succ :=
  finRotate_of_lt i.isLt

lemma twistedRotation_castSucc (g : G) (n : ℕ) (h : Fin (n+1) → G) (i : Fin n) :
    twistedRotation g n h i.castSucc = h i.succ := by
  simp [twistedRotation, Fin.castSucc_ne_last]

lemma twistedRotation_last (g : G) (n : ℕ) (h : Fin (n+1) → G) :
    twistedRotation g n h (Fin.last n) = g*h 0 := by
  simp [twistedRotation]

lemma complex_sign_odd (m : ℕ) : (-1 : ℂ)^(2*m+1) = -1 := by
  rw [pow_add, pow_mul]
  norm_num

lemma rotation_pfaffian (m : ℕ) (B : Fin (2*m+1+1) → Fin (2*m+1+1) → ℂ) :
    pfaffian (m+1) (fun i j => B (finRotate _ i) (finRotate _ j)) =
      -pfaffian (m+1) B := by
  refine (pfaffian_perm (m+1) B (finRotate (2*m+1+1))).trans ?_
  change Equiv.Perm.sign (finRotate (2*m+1+1)) • pfaffian (m+1) B = _
  rw [sign_finRotate]
  have he : 2*m+1+1-1 = 2*m+1 := by omega
  rw [he, pow_add, pow_mul]
  norm_num [Units.smul_def]

lemma twisted_pfaffian (g : G) (β : G → G → ℂ)
    (hβ : ∀ x y, β x y = -β y x)
    (hlift : ∀ (r s : ℤ) x y, β (g^r*x) (g^s*y) = β x y + s - r)
    (m : ℕ) (h : Fin (2*m+1+1) → G) :
    pfaffian (m+1) (fun i j => β (twistedRotation g (2*m+1) h i)
        (twistedRotation g (2*m+1) h j)) =
      -pfaffian (m+1) (fun i j => β (h i) (h j)) +
        detector m (fun i j => β (h i.succ) (h j.succ)) := by
  classical
  let B : Fin (2*m+1+1) → Fin (2*m+1+1) → ℂ :=
    fun i j => β (h (finRotate _ i)) (h (finRotate _ j))
  have he : (fun i j => β (twistedRotation g (2*m+1) h i)
      (twistedRotation g (2*m+1) h j)) =
      (fun i j => B i j + (if j = Fin.last (2*m+1) then 1 else 0) -
        (if i = Fin.last (2*m+1) then 1 else 0)) := by
    funext i j
    simp only [twistedRotation, hlift, B, Int.cast_ite, Int.cast_one, Int.cast_zero]
  change pfaffian (m+1) ((fun i j => β (twistedRotation g (2*m+1) h i)
    (twistedRotation g (2*m+1) h j)) : Fin (2*m+1+1) → Fin (2*m+1+1) → ℂ) = _
  rw [he]
  refine (pfaffian_lift_basis m B (fun i j => hβ _ _) (Fin.last (2*m+1))).trans ?_
  have hm : (fun i j => B ((Fin.last (2*m+1)).succAbove i)
      ((Fin.last (2*m+1)).succAbove j)) = (fun i j => β (h i.succ) (h j.succ)) := by
    simp only [B, Fin.succAbove_last, finRotate_castSucc]
  rw [hm, Fin.val_last, complex_sign_odd, neg_one_mul, sub_neg_eq_add]
  exact congrArg (fun z => z + _) (rotation_pfaffian m (fun i j => β (h i) (h j)))

end Detector

namespace Paths

open scoped BigOperators

def weightedSum {A : Type*} (v : A →₀ ℂ) (f : A → ℂ) : ℂ :=
  v.sum fun a z => z*f a

lemma weightedSum_congr {A : Type*} (v : A →₀ ℂ) {f g : A → ℂ}
    (h : ∀ a, f a = g a) : weightedSum v f = weightedSum v g := by
  exact congrArg (weightedSum v) (funext h)

lemma weightedSum_add {A : Type*} (v : A →₀ ℂ) (f g : A → ℂ) :
    weightedSum v (fun a => f a+g a) = weightedSum v f+weightedSum v g := by
  simp only [weightedSum,Finsupp.sum,mul_add,Finset.sum_add_distrib]

lemma weightedSum_neg {A : Type*} (v : A →₀ ℂ) (f : A → ℂ) :
    weightedSum v (fun a => -f a) = -weightedSum v f := by
  simp only [weightedSum,Finsupp.sum,mul_neg,Finset.sum_neg_distrib]

lemma weightedSum_sum {A I : Type*} (v : A →₀ ℂ) (s : Finset I) (f : I → A → ℂ) :
    weightedSum v (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, weightedSum v (f i) := by
  simp only [weightedSum,Finsupp.sum,Finset.mul_sum]
  rw [Finset.sum_comm]

lemma weightedSum_const_mul {A : Type*} (v : A →₀ ℂ) (c : ℂ) (f : A → ℂ) :
    weightedSum v (fun a => c*f a) = c*weightedSum v f := by
  simp only [weightedSum,Finsupp.sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

lemma weightedSum_mapDomain {A B : Type*} (v : A →₀ ℂ) (f : A → B) (p : B → ℂ) :
    weightedSum (v.mapDomain f) p = weightedSum v (p ∘ f) := by
  exact Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)

variable {G ι : Type*} [Group G] [Fintype ι]

lemma weightedSum_twist (e : GroupMatrix (G := G) (ι := ι)) (g : G) (n : ℕ)
    (p : Orbit g n → ℂ) :
    weightedSum (pathVector e g n) (p ∘ orbitTwist g n) = weightedSum (pathVector e g n) p := by
  rw [← weightedSum_mapDomain,pathVector_twist]

lemma weightedSum_deleteEntry (e : GroupMatrix (G := G) (ι := ι)) (he : e*e=e)
    (g : G) (n : ℕ) (i : Fin (n+2)) (p : Orbit g n → ℂ) :
    weightedSum (pathVector e g (n+1)) (p ∘ deleteEntry g n i) =
      weightedSum (pathVector e g n) p := by
  rw [← weightedSum_mapDomain,pathVector_deleteEntry e he]

end Paths

namespace Detector

open scoped BigOperators

open BassTrace.Paths

section

variable {G : Type*} [Group G]

lemma twist_eq_twistedRotation (g : G) (n : ℕ) (h : Fin (n+1) → G) :
    twist g n h = twistedRotation g n h := by
  funext i
  induction i using Fin.lastCases with
  | last => simp only [twist_last,twistedRotation_last]
  | cast i => simp only [twist_castSucc,twistedRotation_castSucc]

variable (g : G) (β : G → G → ℂ)
    (hc : ∀ (c : Subgroup.centralizer ({g} : Set G)) h k, β (c*h) (c*k) = β h k)

def orbitPfaffian (m : ℕ) : Orbit g (2*m+1) → ℂ :=
  Quotient.lift (fun h => pfaffian (m+1) (fun i j => β (h i) (h j))) (by
    rintro h k ⟨c,hh⟩
    have hk : k = fun i => c*h i := funext fun i => (hh i).symm
    rw [hk]
    simp only [hc])

def orbitDetector (m : ℕ) : Orbit g (2*m) → ℂ :=
  Quotient.lift (fun h => detector m (fun i j => β (h i) (h j))) (by
    rintro h k ⟨c,hh⟩
    have hk : k = fun i => c*h i := funext fun i => (hh i).symm
    rw [hk]
    simp only [hc])

lemma orbitPfaffian_twist (hβ : ∀ x y, β x y = -β y x)
    (hl : ∀ (r s : ℤ) x y, β (g^r*x) (g^s*y) = β x y+s-r)
    (m : ℕ) (q : Orbit g (2*m+1)) :
    orbitPfaffian g β hc m (orbitTwist g (2*m+1) q) =
      -orbitPfaffian g β hc m q +
        orbitDetector g β hc m (deleteEntry g (2*m) 0 q) := by
  induction q using Quotient.inductionOn with | _ h =>
    change pfaffian (m+1) (fun i j => β (twist g (2*m+1) h i) (twist g (2*m+1) h j)) = _
    rw [twist_eq_twistedRotation,twisted_pfaffian g β hβ hl]
    rfl

variable {ι : Type*} [Fintype ι]

def pfaffianSum (e : GroupMatrix (G := G) (ι := ι)) : ℕ → ℂ
  | 0 => totalWeight e g 0
  | m+1 => weightedSum (pathVector e g (2*m+1)) (orbitPfaffian g β hc m)

def detectorSum (e : GroupMatrix (G := G) (ι := ι)) (m : ℕ) : ℂ :=
  weightedSum (pathVector e g (2*m)) (orbitDetector g β hc m)

lemma pfaffianSum_twist (e : GroupMatrix (G := G) (ι := ι)) (he : e*e=e)
    (hβ : ∀ x y, β x y = -β y x)
    (hl : ∀ (r s : ℤ) x y, β (g^r*x) (g^s*y) = β x y+s-r) (m : ℕ) :
    2*pfaffianSum g β hc e (m+1) = detectorSum g β hc e m := by
  have ht := weightedSum_twist e g (2*m+1) (orbitPfaffian g β hc m)
  have hv : weightedSum (pathVector e g (2*m+1))
      ((orbitPfaffian g β hc m) ∘ orbitTwist g (2*m+1)) =
      -pfaffianSum g β hc e (m+1) + detectorSum g β hc e m := by
    simp only [Function.comp_def]
    rw [weightedSum_congr _ (fun q => orbitPfaffian_twist g β hc hβ hl m q),
      weightedSum_add,weightedSum_neg]
    change -pfaffianSum g β hc e (m+1) + weightedSum _
      (orbitDetector g β hc m ∘ deleteEntry g (2*m) 0) = _
    rw [weightedSum_deleteEntry e he]
    rfl
  change _ = pfaffianSum g β hc e (m+1) at ht
  rw [ht] at hv
  linear_combination hv

end

lemma pfaffian_zero (B : Fin (2*0) → Fin (2*0) → ℂ) : pfaffian 0 B = 1 := by
  have ht : (⟨((0 : ℕ).factorial : ℂ)⁻¹ • (twoForm B)^0,
      Submodule.smul_mem _ _ (homogeneous_pow (twoForm_mem B) 0)⟩ :
      ⋀[ℂ]^(2*0) (CoordinateSpace (Fin (2*0)))) = topVolume 0 := by
    apply Subtype.ext
    simp [topVolume]
  exact (congrArg (topCoefficient 0) ht).trans (topCoefficient_topVolume 0)

lemma detector_zero (B : Fin (2*0+1) → Fin (2*0+1) → ℂ)
    (hB : ∀ i j, B i j = -B j i) : detector 0 B = 1 := by
  rw [detector_pfaffian_sum 0 B hB]
  simp [pfaffian_zero]

lemma alternating_sum_odd (m : ℕ) : ∑ i : Fin (2*m+1), (-1:ℂ)^i.val = 1 := by
  induction m with
  | zero => simp
  | succ m hm =>
    change (∑ i : Fin (2*m+1+1+1), (-1:ℂ)^i.val) = 1
    rw [Fin.sum_univ_castSucc,Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last,hm,pow_succ]
    ring

variable {G : Type*} [Group G] (g : G) (β : G → G → ℂ)
    (hc : ∀ (c : Subgroup.centralizer ({g} : Set G)) h k, β (c*h) (c*k) = β h k)

lemma orbitDetector_zero (hβ : ∀ x y, β x y = -β y x) (q : Orbit g 0) :
    orbitDetector g β hc 0 q = 1 := by
  induction q using Quotient.inductionOn with | _ h =>
    exact detector_zero _ (fun i j => hβ _ _)

lemma orbitDetector_succ (hβ : ∀ x y, β x y = -β y x) (m : ℕ)
    (q : Orbit g (2*(m+1))) : orbitDetector g β hc (m+1) q =
      ∑ i : Fin (2*(m+1)+1), (-1:ℂ)^i.val *
        orbitPfaffian g β hc m (deleteEntry g (2*m+1) i q) := by
  induction q using Quotient.inductionOn with | _ h =>
    exact detector_pfaffian_sum (m+1) _ (fun i j => hβ _ _)

variable {ι : Type*} [Fintype ι]

lemma detectorSum_eq_pfaffianSum (e : GroupMatrix (G := G) (ι := ι)) (he : e*e=e)
    (hβ : ∀ x y, β x y = -β y x) (m : ℕ) :
    detectorSum g β hc e m = pfaffianSum g β hc e m := by
  cases m with
  | zero =>
    unfold detectorSum
    rw [weightedSum_congr _ (orbitDetector_zero g β hc hβ)]
    simp only [weightedSum,mul_one,pfaffianSum,totalWeight]
  | succ m =>
    unfold detectorSum
    rw [weightedSum_congr _ (orbitDetector_succ g β hc hβ m),weightedSum_sum]
    simp only [weightedSum_const_mul]
    have hv (i : Fin (2*(m+1)+1)) : weightedSum (pathVector e g (2*(m+1)))
        (fun q => orbitPfaffian g β hc m (deleteEntry g (2*m+1) i q)) =
        pfaffianSum g β hc e (m+1) := by
      exact weightedSum_deleteEntry e he g (2*m+1) i (orbitPfaffian g β hc m)
    simp_rw [hv]
    rw [← Finset.sum_mul,alternating_sum_odd,one_mul]

lemma pfaffianSum_recurrence (e : GroupMatrix (G := G) (ι := ι)) (he : e*e=e)
    (hβ : ∀ x y, β x y = -β y x)
    (hl : ∀ (r s : ℤ) x y, β (g^r*x) (g^s*y) = β x y+s-r) (m : ℕ) :
    2*pfaffianSum g β hc e (m+1) = pfaffianSum g β hc e m := by
  rw [pfaffianSum_twist g β hc e he hβ hl,detectorSum_eq_pfaffianSum g β hc e he hβ]

lemma pfaffianSum_value (e : GroupMatrix (G := G) (ι := ι)) (he : e*e=e)
    (hβ : ∀ x y, β x y = -β y x)
    (hl : ∀ (r s : ℤ) x y, β (g^r*x) (g^s*y) = β x y+s-r) (m : ℕ) :
    pfaffianSum g β hc e m = (2:ℂ)⁻¹^m*totalWeight e g 0 := by
  induction m with
  | zero => simp [pfaffianSum]
  | succ m hm =>
    have hr := pfaffianSum_recurrence g β hc e he hβ hl m
    rw [hm] at hr
    rw [pow_succ]
    linear_combination (1/2:ℂ)*hr

lemma detectorSum_value (e : GroupMatrix (G := G) (ι := ι)) (he : e*e=e)
    (hβ : ∀ x y, β x y = -β y x)
    (hl : ∀ (r s : ℤ) x y, β (g^r*x) (g^s*y) = β x y+s-r) (m : ℕ) :
    detectorSum g β hc e m = (2:ℂ)⁻¹^m*totalWeight e g 0 := by
  rw [detectorSum_eq_pfaffianSum g β hc e he hβ,pfaffianSum_value g β hc e he hβ hl]

end Detector

end BassTrace

end

end OAI
