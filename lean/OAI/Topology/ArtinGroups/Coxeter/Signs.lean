import Mathlib
import OAI.Topology.ArtinGroups.Quivers.ReversibleQuiver

namespace OAI

namespace HarmonicArtin.CoxeterExchange

open scoped Classical

variable {W : Type*} [Group W]

abbrev Signs (W : Type*) := Multiplicative (W → ZMod 2)

noncomputable def signAction : W →* MulAut (Signs W) where
  toFun g :=
    { toFun f := Multiplicative.ofAdd (fun t => Multiplicative.toAdd f (g⁻¹ * t * g))
      invFun f := Multiplicative.ofAdd (fun t => Multiplicative.toAdd f (g * t * g⁻¹))
      left_inv f := by
        apply Multiplicative.toAdd.injective
        funext t
        change Multiplicative.toAdd f (g⁻¹ * (g * t * g⁻¹) * g) = Multiplicative.toAdd f t
        group
      right_inv f := by
        apply Multiplicative.toAdd.injective
        funext t
        change Multiplicative.toAdd f (g * (g⁻¹ * t * g) * g⁻¹) = Multiplicative.toAdd f t
        group
      map_mul' f h := rfl }
  map_one' := by
    apply MulEquiv.ext
    intro f
    apply Multiplicative.toAdd.injective
    funext t
    simp
  map_mul' g h := by
    apply MulEquiv.ext
    intro f
    apply Multiplicative.toAdd.injective
    funext t
    change Multiplicative.toAdd f ((g*h)⁻¹*t*(g*h)) =
      Multiplicative.toAdd f (h⁻¹*(g⁻¹*t*g)*h)
    group

abbrev SignedGroup (W : Type*) [Group W] := Signs W ⋊[signAction] W

def coeff (x : SignedGroup W) : W → ZMod 2 := Multiplicative.toAdd x.left

@[simp] lemma coeff_one : coeff (1 : SignedGroup W) = 0 := rfl

@[simp] lemma coeff_mul (x y : SignedGroup W) (t : W) :
    coeff (x*y) t = coeff x t + coeff y (x.right⁻¹ * t * x.right) := rfl

noncomputable def delta (s : W) : W → ZMod 2 := fun t => if t=s then 1 else 0

lemma delta_conj (g s t : W) : delta s (g⁻¹*t*g) = delta (g*s*g⁻¹) t := by
  unfold delta
  congr 1
  apply propext
  constructor
  · intro h
    calc t = g*(g⁻¹*t*g)*g⁻¹ := by group
         _ = g*s*g⁻¹ := by rw [h]
  · intro h
    rw [h]
    group

noncomputable def signedGenerator (s : W) : SignedGroup W :=
  ⟨Multiplicative.ofAdd (delta s),s⟩

@[simp] lemma signedGenerator_right (s : W) : (signedGenerator s).right = s := rfl
@[simp] lemma coeff_signedGenerator (s : W) : coeff (signedGenerator s) = delta s := rfl

lemma coeff_pair (s t r : W) (hs : s*s=1) :
    coeff (signedGenerator s * signedGenerator t) r =
      delta s r + delta (s*t*s) r := by
  rw [coeff_mul,coeff_signedGenerator,coeff_signedGenerator,signedGenerator_right,delta_conj]
  rw [inv_eq_of_mul_eq_one_left hs]

lemma braid_power_transport (s t : W) (n : ℕ) :
    s*(t*s)^n = (s*t)^n*s := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ,pow_succ,← mul_assoc,ih]
    group

lemma pair_pow_conj_first (s t : W) (hs : s*s=1) (ht : t*t=1) (n : ℕ) :
    (s*t)^n*s*((s*t)^n)⁻¹ = (s*t)^(2*n)*s := by
  have hsi : s⁻¹=s := inv_eq_of_mul_eq_one_left hs
  have hti : t⁻¹=t := inv_eq_of_mul_eq_one_left ht
  rw [← inv_pow,mul_inv_rev,hsi,hti,mul_assoc,braid_power_transport s t,
    ← mul_assoc,← pow_add]
  congr 2
  omega

lemma pair_pow_conj_second (s t : W) (hs : s*s=1) (ht : t*t=1) (n : ℕ) :
    (s*t)^n*(s*t*s)*((s*t)^n)⁻¹ = (s*t)^(2*n+1)*s := by
  have h := pair_pow_conj_first s t hs ht n
  calc
    _ = ((s*t)^n*(s*t))*s*((s*t)^n)⁻¹ := by group
    _ = ((s*t)*(s*t)^n)*s*((s*t)^n)⁻¹ := by rw [← pow_succ,pow_succ']
    _ = (s*t)*((s*t)^n*s*((s*t)^n)⁻¹) := by group
    _ = (s*t)*((s*t)^(2*n)*s) := by rw [h]
    _ = _ := by rw [← mul_assoc,← pow_succ']

lemma signed_pair_power_right (s t : W) (n : ℕ) :
    ((signedGenerator s * signedGenerator t)^n).right = (s*t)^n := by
  exact map_pow (SemidirectProduct.rightHom) _ n

lemma coeff_signed_pair_power (s t : W) (hs : s*s=1) (ht : t*t=1) (n : ℕ) (r : W) :
    coeff ((signedGenerator s * signedGenerator t)^n) r =
      ∑ j ∈ Finset.range (2*n), delta ((s*t)^j*s) r := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ,coeff_mul,ih,signed_pair_power_right,coeff_pair s t _ hs]
    rw [delta_conj,delta_conj,pair_pow_conj_first s t hs ht,pair_pow_conj_second s t hs ht]
    have hn : 2*(n+1)=(2*n+1)+1 := by omega
    rw [hn,Finset.sum_range_succ,Finset.sum_range_succ]
    simp only [add_assoc]

lemma signed_pair_power_eq_one (s t : W) (hs : s*s=1) (ht : t*t=1) (n : ℕ)
    (hn : (s*t)^n=1) : (signedGenerator s * signedGenerator t)^n=1 := by
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    funext r
    change coeff ((signedGenerator s * signedGenerator t)^n) r = 0
    rw [coeff_signed_pair_power s t hs ht]
    have he : 2*n=n+n := by omega
    rw [he,Finset.sum_range_add]
    have hh : (∑ j ∈ Finset.range n,delta ((s*t)^(n+j)*s) r) =
        ∑ j ∈ Finset.range n,delta ((s*t)^j*s) r := by
      apply Finset.sum_congr rfl
      intro j _
      rw [pow_add,hn,one_mul]
    rw [hh]
    exact CharTwo.add_self_eq_zero _
  · simpa only [signed_pair_power_right,SemidirectProduct.one_right] using hn

variable {B : Type*} {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

noncomputable def signedLift : W →* SignedGroup W :=
  cs.lift ⟨fun i => signedGenerator (cs.simple i), fun i j =>
    signed_pair_power_eq_one _ _ (cs.simple_mul_simple_self i)
      (cs.simple_mul_simple_self j) (M i j) (cs.simple_mul_simple_pow i j)⟩

@[simp] lemma signedLift_simple (i : B) :
    signedLift cs (cs.simple i) = signedGenerator (cs.simple i) := by
  exact cs.lift_apply_simple _ i

@[simp] lemma signedLift_right (w : W) : (signedLift cs w).right = w := by
  have h : SemidirectProduct.rightHom.comp (signedLift cs) = MonoidHom.id W := by
    apply cs.ext_simple
    intro i
    simp
  exact DFunLike.congr_fun h w

lemma coeff_wordProd (w : List B) (t : W) :
    coeff (signedLift cs (cs.wordProd w)) t =
      ((cs.leftInvSeq w).map (fun r => delta r t)).sum := by
  induction w generalizing t with
  | nil => simp
  | cons i w ih =>
    rw [cs.wordProd_cons,map_mul,coeff_mul,signedLift_simple,
      coeff_signedGenerator,signedGenerator_right,ih]
    simp only [CoxeterSystem.leftInvSeq,List.map_cons,List.map_map,List.sum_cons]
    congr 1
    apply congrArg List.sum
    apply List.map_congr_left
    intro r _
    exact delta_conj (cs.simple i) r t

omit [Group W] in
lemma sum_delta_nodup (l : List W) (h : l.Nodup) (t : W) :
    (l.map (fun r => delta r t)).sum = if t ∈ l then 1 else 0 := by
  classical
  induction l with
  | nil => simp
  | cons r l ih =>
    obtain ⟨hr,hl⟩ := List.nodup_cons.mp h
    rw [List.map_cons,List.sum_cons,ih hl]
    by_cases ht : t=r
    · subst t
      simp [delta,hr]
    · simp [delta,ht]

lemma coeff_reduced (w : List B) (hw : cs.IsReduced w) (t : W) :
    coeff (signedLift cs (cs.wordProd w)) t = if t ∈ cs.leftInvSeq w then 1 else 0 := by
  rw [coeff_wordProd, sum_delta_nodup _ (hw.nodup_leftInvSeq)]

lemma reduced_invSeq_membership {u v : List B}
    (hu : cs.IsReduced u) (hv : cs.IsReduced v) (h : cs.wordProd u = cs.wordProd v)
    (t : W) : t ∈ cs.leftInvSeq u ↔ t ∈ cs.leftInvSeq v := by
  have hh := congrArg (fun g => coeff (signedLift cs g) t) h
  rw [coeff_reduced cs u hu,coeff_reduced cs v hv] at hh
  by_cases h₁ : t ∈ cs.leftInvSeq u <;> by_cases h₂ : t ∈ cs.leftInvSeq v <;>
    simp_all

lemma simple_mem_leftInvSeq_of_shorter {w : List B} (hw : cs.IsReduced w) (i : B)
    (hi : cs.length (cs.simple i * cs.wordProd w) < cs.length (cs.wordProd w)) :
    cs.simple i ∈ cs.leftInvSeq w := by
  obtain ⟨u,hu,he⟩ := cs.exists_isReduced (cs.simple i * cs.wordProd w)
  have hw' : cs.wordProd (i :: u) = cs.wordProd w := by
    rw [cs.wordProd_cons, ← he,cs.simple_mul_simple_cancel_left]
  have hr : cs.IsReduced (i :: u) := by
    change cs.length (cs.wordProd (i :: u)) = (i :: u).length
    rw [hw',List.length_cons, ← hu.eq, ← he]
    rcases cs.length_simple_mul (cs.wordProd w) i with h | h
    · omega
    · omega
  exact (reduced_invSeq_membership cs hr hw hw' (cs.simple i)).mp (by
    simp [CoxeterSystem.leftInvSeq])

lemma simple_exchange {w : List B} (hw : cs.IsReduced w) (i : B)
    (hi : cs.length (cs.simple i * cs.wordProd w) < cs.length (cs.wordProd w)) :
    ∃ j, j < w.length ∧ cs.simple i * cs.wordProd w = cs.wordProd (w.eraseIdx j) := by
  obtain ⟨j,hj,hv⟩ := List.mem_iff_getElem.mp (simple_mem_leftInvSeq_of_shorter cs hw i hi)
  refine ⟨j,by simpa using hj,?_⟩
  rw [← hv, ← List.getD_eq_getElem _ 1 hj]
  exact cs.getD_leftInvSeq_mul_wordProd w j

end HarmonicArtin.CoxeterExchange

end OAI
