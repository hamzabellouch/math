import Mathlib
import OAI.Topology.Homotopy.BasedMaps

namespace OAI

/-! The path-space homotopy fiber and exactness at its projection. -/

noncomputable section
universe u v w


namespace NearbyLagrangian.HomotopyFiber
open ContinuousMap
open scoped Topology Topology.Homotopy
open BasedHomotopy
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def Fiber (e : C(X,Y)) (y : Y) :=
  {z : X × C(unitInterval,Y) // z.2 0 = e z.1 ∧ z.2 1 = y}

instance (e : C(X,Y)) (y : Y) : TopologicalSpace (Fiber e y) := inferInstanceAs
  (TopologicalSpace {z : X × C(unitInterval,Y) // z.2 0 = e z.1 ∧ z.2 1 = y})

def base (e : C(X,Y)) (x : X) : Fiber e (e x) :=
  ⟨(x,ContinuousMap.const _ (e x)),rfl,rfl⟩

def projection (e : C(X,Y)) (y : Y) : C(Fiber e y,X) :=
  ⟨fun z => z.1.1,continuous_fst.comp continuous_subtype_val⟩

@[simp] theorem projection_base (e : C(X,Y)) (x : X) :
    projection e (e x) (base e x) = x := rfl

variable {N : Type*}

def projectionNullhomotopy (e : C(X,Y)) (x : X)
    (f : GenLoop N (Fiber e (e x)) (base e x)) :
    (loopMap e rfl (loopMap (projection e (e x)) rfl f)).1.HomotopyRel (ContinuousMap.const _ (e x)) (Cube.boundary N) where
  toFun z := (f z.2).1.2 z.1
  continuous_toFun := by
    exact ((continuous_snd.comp (continuous_subtype_val.comp (f.1.continuous.comp continuous_snd))).eval continuous_fst)
  map_zero_left t := (f t).2.1
  map_one_left t := (f t).2.2
  prop' s t ht := by
    change (f t).1.2 s = e (f t).1.1
    rw [GenLoop.boundary f t ht]
    rfl

def liftNullhomotopy (e : C(X,Y)) (x : X) (f : GenLoop N X x)
    (H : (loopMap e rfl f).1.HomotopyRel (ContinuousMap.const _ (e x)) (Cube.boundary N)) :
    GenLoop N (Fiber e (e x)) (base e x) :=
  ⟨⟨fun t => ⟨(f t,(H.toContinuousMap.comp ContinuousMap.prodSwap).curry t),
      H.map_zero_left t,H.map_one_left t⟩,by
      apply Continuous.subtype_mk
      exact f.1.continuous.prodMk (H.toContinuousMap.comp ContinuousMap.prodSwap).curry.continuous⟩,
    by
      intro t ht
      apply Subtype.ext
      apply Prod.ext (GenLoop.boundary f t ht)
      ext s
      exact (H.prop s t ht).trans (congrArg e (GenLoop.boundary f t ht))⟩

@[simp] theorem projection_liftNullhomotopy (e : C(X,Y)) (x : X) (f : GenLoop N X x)
    (H : (loopMap e rfl f).1.HomotopyRel (ContinuousMap.const _ (e x)) (Cube.boundary N)) :
    loopMap (projection e (e x)) rfl (liftNullhomotopy e x f H) = f := by ext; rfl

theorem kernel_eq_projection_range [DecidableEq N] [Nonempty N]
    (e : C(X,Y)) (x : X) (a : HomotopyGroup N X x) :
    groupMap e rfl a = 1 ↔
      ∃ b : HomotopyGroup N (Fiber e (e x)) (base e x),
        groupMap (projection e (e x)) rfl b = a := by
  induction a using Quotient.inductionOn with
  | h f =>
    constructor
    · intro h
      change (⟦loopMap e rfl f⟧ : HomotopyGroup N Y (e x)) = ⟦GenLoop.const⟧ at h
      obtain ⟨H⟩ := Quotient.exact h
      exact ⟨⟦liftNullhomotopy e x f H⟧,congrArg Quotient.mk'' (projection_liftNullhomotopy e x f H)⟩
    · rintro ⟨b,hb⟩
      rw [← hb]
      induction b using Quotient.inductionOn with
      | h g =>
        change (⟦loopMap e rfl (loopMap (projection e (e x)) rfl g)⟧ : HomotopyGroup N Y (e x)) = ⟦GenLoop.const⟧
        exact Quotient.sound ⟨projectionNullhomotopy e x g⟩

end NearbyLagrangian.HomotopyFiber

end

noncomputable section
universe u v w


namespace NearbyLagrangian.HomotopyFiber
open ContinuousMap Set
open scoped Topology Topology.Homotopy
open BasedHomotopy

def frontTime (s r : unitInterval) : unitInterval := projIcc 0 1 zero_le_one ((s:ℝ)-2*r)
def backTime (s r : unitInterval) : unitInterval := projIcc 0 1 zero_le_one ((2*(r:ℝ)-s)/(2-s))

lemma continuous_frontTime : Continuous (fun z : unitInterval × unitInterval => frontTime z.1 z.2) := by
  unfold frontTime
  fun_prop

lemma continuous_backTime : Continuous (fun z : unitInterval × unitInterval => backTime z.1 z.2) := by
  unfold backTime
  apply continuous_projIcc.comp
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro z
    have := z.1.property.2
    linarith

@[simp] lemma frontTime_zero_right (s : unitInterval) : frontTime s 0 = s := by
  change projIcc 0 1 zero_le_one ((s:ℝ)-2*0) = s
  simp only [mul_zero,sub_zero]
  exact projIcc_val _ s

@[simp] lemma backTime_one_right (s : unitInterval) : backTime s 1 = 1 := by
  unfold backTime
  have hs : (2:ℝ)-s ≠ 0 := by linarith [s.property.2]
  simp [hs]

@[simp] lemma backTime_zero_left (r : unitInterval) : backTime 0 r = r := by
  change projIcc 0 1 zero_le_one ((2*(r:ℝ)-0)/(2-0)) = r
  have he : (2*(r:ℝ)-(0:ℝ))/(2-(0:ℝ)) = r := by ring
  rw [he]
  exact projIcc_val _ r

lemma frontTime_seam {s r : unitInterval} (h : 2*(r:ℝ)=s) : frontTime s r = 0 := by
  unfold frontTime
  rw [h,sub_self]
  exact projIcc_left _

lemma backTime_seam {s r : unitInterval} (h : 2*(r:ℝ)=s) : backTime s r = 0 := by
  unfold backTime
  rw [h,sub_self,zero_div]
  exact projIcc_left _

variable {A X Y : Type*} [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace Y]
variable (e : C(X,Y)) (x : X) (f : C(A,Fiber e (e x)))
variable (H : ((projection e (e x)).comp f).Homotopy (ContinuousMap.const A x))

def deformValue (z : (unitInterval × A) × unitInterval) : Y :=
  if 2*(z.2:ℝ) ≤ z.1.1 then e (H (frontTime z.1.1 z.2,z.1.2))
  else (f z.1.2).1.2 (backTime z.1.1 z.2)

lemma continuous_deformValue : Continuous (deformValue e x f H) := by
  unfold deformValue
  apply continuous_if_le
  · fun_prop
  · fun_prop
  · apply Continuous.continuousOn
    apply e.continuous.comp
    apply H.continuous.comp
    exact (continuous_frontTime.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)).prodMk
      (continuous_snd.comp continuous_fst)
  · apply Continuous.continuousOn
    exact (continuous_snd.comp (continuous_subtype_val.comp
      (f.continuous.comp (continuous_snd.comp continuous_fst)))).eval
        (continuous_backTime.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd))
  · intro z hz
    rw [frontTime_seam hz,backTime_seam hz,H.apply_zero]
    exact (f z.1.2).2.1.symm

@[simp] lemma deformValue_start (s : unitInterval) (a : A) :
    deformValue e x f H ((s,a),0) = e (H (s,a)) := by
  change (if 2*(0:ℝ) ≤ s then e (H (frontTime s 0,a)) else (f a).1.2 (backTime s 0)) = e (H (s,a))
  simp only [mul_zero,ite_eq_left s.property.1,frontTime_zero_right]

@[simp] lemma deformValue_end (s : unitInterval) (a : A) :
    deformValue e x f H ((s,a),1) = e x := by
  change (if 2*(1:ℝ) ≤ s then e (H (frontTime s 1,a)) else (f a).1.2 (backTime s 1)) = e x
  have hs : ¬ 2*(1:ℝ) ≤ (s:ℝ) := by linarith [s.property.2]
  rw [ite_eq_right hs,backTime_one_right]
  exact (f a).2.2

@[simp] lemma deformValue_zero (a : A) (r : unitInterval) :
    deformValue e x f H ((0,a),r) = (f a).1.2 r := by
  unfold deformValue
  split_ifs with hr
  · have he : r = 0 := Subtype.ext (by dsimp at hr ⊢; linarith [r.property.1])
    rw [he,frontTime_zero_right,H.apply_zero]
    exact (f a).2.1.symm
  · rw [backTime_zero_left]

def deformPath : C(unitInterval × A,C(unitInterval,Y)) :=
  (⟨deformValue e x f H,continuous_deformValue e x f H⟩ : C((unitInterval × A) × unitInterval,Y)).curry

def deformFiber : C(unitInterval × A,Fiber e (e x)) where
  toFun z := ⟨(H z,deformPath e x f H z),deformValue_start e x f H z.1 z.2,deformValue_end e x f H z.1 z.2⟩
  continuous_toFun := (H.continuous.prodMk (deformPath e x f H).continuous).subtype_mk _

@[simp] lemma deformFiber_zero (a : A) : deformFiber e x f H (0,a) = f a := by
  apply Subtype.ext
  apply Prod.ext
  · exact H.apply_zero a
  · ext r
    exact deformValue_zero e x f H a r

def loopInclusion : C(Path (e x) (e x),Fiber e (e x)) where
  toFun p := ⟨(x,p.toContinuousMap),p.source,p.target⟩
  continuous_toFun := (continuous_const.prodMk continuous_induced_dom).subtype_mk _

@[simp] lemma loopInclusion_base : loopInclusion e x (Path.refl (e x)) = base e x := rfl

def loopRepresentative : C(A,Path (e x) (e x)) where
  toFun a := {
    toContinuousMap := deformPath e x f H (1,a)
    source' := by
      change deformValue e x f H ((1,a),0) = e x
      rw [deformValue_start,H.apply_one,ContinuousMap.const_apply]
    target' := deformValue_end e x f H 1 a }
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    exact (continuous_deformValue e x f H).comp ((continuous_const.prodMk continuous_fst).prodMk continuous_snd)

def deformHomotopy : f.Homotopy ((loopInclusion e x).comp (loopRepresentative e x f H)) where
  toContinuousMap := deformFiber e x f H
  map_zero_left := deformFiber_zero e x f H
  map_one_left a := by
    apply Subtype.ext
    apply Prod.ext
    · exact H.apply_one a
    · rfl

lemma deformValue_fixed (a : A) (ha : f a = base e x) (hH : ∀ s, H (s,a) = x)
    (s r : unitInterval) : deformValue e x f H ((s,a),r) = e x := by
  unfold deformValue
  split_ifs
  · rw [hH]
  · rw [ha]
    rfl

lemma deformFiber_fixed (a : A) (ha : f a = base e x) (hH : ∀ s, H (s,a) = x)
    (s : unitInterval) : deformFiber e x f H (s,a) = base e x := by
  apply Subtype.ext
  apply Prod.ext (hH s)
  ext r
  exact deformValue_fixed e x f H a ha hH s r

lemma loopRepresentative_fixed (a : A) (ha : f a = base e x) (hH : ∀ s, H (s,a) = x) :
    loopRepresentative e x f H a = Path.refl (e x) := by
  apply Path.ext
  funext r
  exact deformValue_fixed e x f H a ha hH 1 r

end NearbyLagrangian.HomotopyFiber

end

noncomputable section
universe u v w


namespace NearbyLagrangian.HomotopyFiber
open ContinuousMap
open scoped Topology Topology.Homotopy
open BasedHomotopy
variable {N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable (e : C(X,Y)) (x : X)

def boundaryRepresentative (f : GenLoop N (Fiber e (e x)) (base e x))
    (H : (loopMap (projection e (e x)) rfl f).1.HomotopyRel
      (ContinuousMap.const _ x) (Cube.boundary N)) :
    GenLoop N (Path (e x) (e x)) (Path.refl (e x)) :=
  ⟨loopRepresentative e x f.1 H.toHomotopy,by
    intro t ht
    apply loopRepresentative_fixed
    · exact GenLoop.boundary f t ht
    · intro s
      exact (H.prop s t ht).trans (congrArg (projection e (e x)) (GenLoop.boundary f t ht))⟩

def boundaryRepresentativeHomotopy (f : GenLoop N (Fiber e (e x)) (base e x))
    (H : (loopMap (projection e (e x)) rfl f).1.HomotopyRel
      (ContinuousMap.const _ x) (Cube.boundary N)) :
    f.1.HomotopyRel (loopMap (loopInclusion e x) rfl (boundaryRepresentative e x f H)).1
      (Cube.boundary N) where
  toHomotopy := deformHomotopy e x f.1 H.toHomotopy
  prop' s t ht := by
    change deformFiber e x f.1 H.toHomotopy (s,t) = f t
    rw [GenLoop.boundary f t ht]
    apply deformFiber_fixed
    · exact GenLoop.boundary f t ht
    · intro r
      exact (H.prop r t ht).trans (congrArg (projection e (e x)) (GenLoop.boundary f t ht))

@[simp] theorem projection_loopInclusion (g : GenLoop N (Path (e x) (e x)) (Path.refl (e x))) :
    loopMap (projection e (e x)) rfl (loopMap (loopInclusion e x) rfl g) = GenLoop.const := by
  ext t
  rfl

theorem projection_kernel_eq_loop_range [DecidableEq N] [Nonempty N]
    (a : HomotopyGroup N (Fiber e (e x)) (base e x)) :
    groupMap (projection e (e x)) rfl a = 1 ↔
      ∃ b : HomotopyGroup N (Path (e x) (e x)) (Path.refl (e x)),
        groupMap (loopInclusion e x) rfl b = a := by
  induction a using Quotient.inductionOn with
  | h f =>
    constructor
    · intro h
      change (⟦loopMap (projection e (e x)) rfl f⟧ : HomotopyGroup N X x) = ⟦GenLoop.const⟧ at h
      obtain ⟨H⟩ := Quotient.exact h
      refine ⟨⟦boundaryRepresentative e x f H⟧, ?_⟩
      exact Quotient.sound ⟨(boundaryRepresentativeHomotopy e x f H).symm⟩
    · rintro ⟨b,hb⟩
      rw [← hb]
      induction b using Quotient.inductionOn with
      | h g =>
        change (⟦loopMap (projection e (e x)) rfl (loopMap (loopInclusion e x) rfl g)⟧ :
          HomotopyGroup N X x) = ⟦GenLoop.const⟧
        exact congrArg Quotient.mk'' (projection_loopInclusion e x g)

end NearbyLagrangian.HomotopyFiber

end

end OAI
