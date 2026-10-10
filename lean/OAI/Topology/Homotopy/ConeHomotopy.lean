import Mathlib
import OAI.Topology.Homotopy.FiberCone

namespace OAI

/-! Right suspension homotopies and suspension of maps and homotopies. -/

noncomputable section
universe u v w
open Set ContinuousMap
open scoped Topology unitInterval

namespace NearbyLagrangian.FiberCone
variable {B A X : Type*} [TopologicalSpace B] [TopologicalSpace A] [TopologicalSpace X]
variable (f : C(A,X)) (p : C(X,B)) (q : C(A,B)) (hf : ∀ a, p (f a) = q a)

def sweepBase : C(unitInterval × X,Susp p) := meridian p

def sweepRay : C(unitInterval × (unitInterval × A),Susp p) where
  toFun z := meridian p (max z.2.1 z.1,f z.2.2)
  continuous_toFun := (meridian p).continuous.comp
    (((continuous_fst.comp continuous_snd).max continuous_fst).prodMk
      (f.continuous.comp (continuous_snd.comp continuous_snd)))

def sweepApex : C(unitInterval × B,Susp p) := (north p).comp ⟨Prod.snd,continuous_snd⟩

lemma sweepRay_bottom (s : unitInterval) (a : A) :
    sweepRay f p (s,(0,a)) = sweepBase p (s,f a) := by
  change meridian p (max 0 s,f a) = meridian p (s,f a)
  rw [max_eq_right (show (0:unitInterval) ≤ s from bot_le)]

include hf in
lemma sweepRay_top (s : unitInterval) (a : A) :
    sweepRay f p (s,(1,a)) = sweepApex p (s,q a) := by
  change meridian p (max 1 s,f a) = north p (q a)
  rw [max_eq_left (show s ≤ (1:unitInterval) from le_top),ray_one,hf]

def sweep : C(unitInterval × Space f q,Susp p) :=
  cylinderLift f q (sweepBase p) (sweepRay f p) (sweepApex p)
    (sweepRay_bottom f p) (sweepRay_top f p q hf)

@[simp] lemma sweep_base (s : unitInterval) (x : X) :
    sweep f p q hf (s,base f q x) = meridian p (s,x) := rfl
@[simp] lemma sweep_ray (s : unitInterval) (ta : unitInterval × A) :
    sweep f p q hf (s,ray f q ta) = meridian p (max ta.1 s,f ta.2) := rfl
@[simp] lemma sweep_apex (s : unitInterval) (b : B) :
    sweep f p q hf (s,apex f q b) = north p b := rfl

lemma sweep_zero (z : Space f q) :
    sweep f p q hf (0,z) = suspMap f p q hf (collapse f p q hf z) := by
  induction z using induction with
  | hbase x => rw [sweep_base,ray_zero,collapse_base,suspMap_south]
  | hray ta =>
    rw [sweep_ray,max_eq_left (show (0:unitInterval) ≤ ta.1 from bot_le),
      collapse_ray,suspMap_meridian]
  | hapex b => rw [sweep_apex,collapse_apex,suspMap_north]

lemma sweep_one (z : Space f q) :
    sweep f p q hf (1,z) = north p (projection f p q hf z) := by
  induction z using induction with
  | hbase x => rw [sweep_base,ray_one,projection_base]
  | hray ta =>
    rw [sweep_ray,max_eq_right (show ta.1 ≤ (1:unitInterval) from le_top),
      ray_one,hf,projection_ray]
  | hapex b => rfl

lemma sweep_over (s : unitInterval) (z : Space f q) :
    suspProjection p (sweep f p q hf (s,z)) = projection f p q hf z := by
  induction z using induction with
  | hbase x => rfl
  | hray ta => exact hf ta.2
  | hapex b => rfl

namespace Contraction
variable {f p q hf} (H : Contraction f p q hf)

def rightRay : C(unitInterval × (unitInterval × X),Susp p) where
  toFun z := sweep f p q hf (horizontal (z.1,z.2.1),
    H.hom (vertical (z.1,z.2.1),base f q z.2.2))
  continuous_toFun := (sweep f p q hf).continuous.comp
    ((horizontal.continuous.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk
      (H.hom.continuous.comp
        ((vertical.continuous.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk
          ((base f q).continuous.comp (continuous_snd.comp continuous_snd)))))

lemma rightRay_bottom (s : unitInterval) (x : X) : H.rightRay (s,(0,x)) = south p (p x) := by
  change sweep f p q hf (horizontal (s,0),H.hom (vertical (s,0),base f q x)) = _
  rw [horizontal_bottom,vertical_bottom,H.at_zero,sweep_base,ray_zero]

lemma rightRay_top (s : unitInterval) (x : X) : H.rightRay (s,(1,x)) = north p (p x) := by
  change sweep f p q hf (horizontal (s,1),H.hom (vertical (s,1),base f q x)) = _
  rcases square_top s with hx | hy
  · rw [hx,sweep_one,H.staysOver,projection_base]
  · rw [hy,H.at_one,projection_base,sweep_apex]

def rightDeformation : C(unitInterval × Susp p,Susp p) :=
  cylinderLift p p ((south p).comp ⟨Prod.snd,continuous_snd⟩) H.rightRay
    ((north p).comp ⟨Prod.snd,continuous_snd⟩) H.rightRay_bottom H.rightRay_top

@[simp] lemma rightDeformation_south (s : unitInterval) (b : B) :
    H.rightDeformation (s,south p b) = south p b := rfl
@[simp] lemma rightDeformation_meridian (s : unitInterval) (tx : unitInterval × X) :
    H.rightDeformation (s,meridian p tx) = H.rightRay (s,tx) := rfl
@[simp] lemma rightDeformation_north (s : unitInterval) (b : B) :
    H.rightDeformation (s,north p b) = north p b := rfl

lemma rightDeformation_zero (z : Susp p) : H.rightDeformation (0,z) = z := by
  induction z using induction with
  | hbase b => rfl
  | hray tx =>
    rw [rightDeformation_meridian]
    change sweep f p q hf (horizontal (0,tx.1),
      H.hom (vertical (0,tx.1),base f q tx.2)) = _
    rw [horizontal_left,vertical_left,H.at_zero,sweep_base]
  | hapex b => rfl

lemma rightDeformation_one (z : Susp p) :
    H.rightDeformation (1,z) = suspMap f p q hf (H.inverse z) := by
  induction z using induction with
  | hbase b => rw [rightDeformation_south,inverse_south,suspMap_south]
  | hray tx =>
    rw [rightDeformation_meridian,inverse_meridian]
    change sweep f p q hf (horizontal (1,tx.1),
      H.hom (vertical (1,tx.1),base f q tx.2)) = _
    rw [horizontal_right,vertical_right,sweep_zero]
  | hapex b => rw [rightDeformation_north,inverse_north,suspMap_north]

lemma rightDeformation_over (s : unitInterval) (z : Susp p) :
    suspProjection p (H.rightDeformation (s,z)) = suspProjection p z := by
  induction z using induction with
  | hbase b => rfl
  | hray tx =>
    rw [rightDeformation_meridian]
    change suspProjection p (sweep f p q hf (horizontal (s,tx.1),
      H.hom (vertical (s,tx.1),base f q tx.2))) = _
    rw [sweep_over,H.staysOver,projection_base]
    rfl
  | hapex b => rfl

def rightHomotopy : ((suspMap f p q hf).comp H.inverse).Homotopy (ContinuousMap.id (Susp p)) :=
  ContinuousMap.Homotopy.symm
    { toContinuousMap := H.rightDeformation
      map_zero_left := H.rightDeformation_zero
      map_one_left := H.rightDeformation_one }

lemma rightHomotopy_over (s : unitInterval) (z : Susp p) :
    suspProjection p (H.rightHomotopy (s,z)) = suspProjection p z :=
  H.rightDeformation_over (unitInterval.symm s) z

end Contraction
end NearbyLagrangian.FiberCone

end

noncomputable section
universe u v w
open Set ContinuousMap
open scoped Topology unitInterval

namespace NearbyLagrangian.FiberCone
variable {B A X Y : Type*} [TopologicalSpace B] [TopologicalSpace A]
  [TopologicalSpace X] [TopologicalSpace Y]

@[simp] lemma suspMap_id (q : C(A,B)) :
    suspMap (ContinuousMap.id A) q q (fun _ => rfl) = ContinuousMap.id (Susp q) := by
  ext z
  induction z using induction with
  | hbase _ => rfl
  | hray _ => rfl
  | hapex _ => rfl

lemma suspMap_comp (f : C(A,X)) (g : C(X,Y)) (p : C(X,B)) (q : C(A,B)) (r : C(Y,B))
    (hf : ∀ a, p (f a) = q a) (hg : ∀ x, r (g x) = p x) :
    (suspMap g r p hg).comp (suspMap f p q hf) =
      suspMap (g.comp f) r q (fun a => (hg (f a)).trans (hf a)) := by
  ext z
  induction z using induction with
  | hbase _ => rfl
  | hray _ => rfl
  | hapex _ => rfl

variable {p : C(X,B)} {q : C(A,B)} {f g : C(A,X)}
  (hf : ∀ a, p (f a) = q a) (hg : ∀ a, p (g a) = q a)
  (H : f.Homotopy g) (hH : ∀ s a, p (H (s,a)) = q a)

def suspHomotopyRay : C(unitInterval × (unitInterval × A),Susp p) :=
  (meridian p).comp ⟨fun z => (z.2.1,H (z.1,z.2.2)),
    (continuous_fst.comp continuous_snd).prodMk
      (H.continuous.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))⟩

include hH in
lemma suspHomotopyRay_bottom (s : unitInterval) (a : A) :
    suspHomotopyRay H (s,(0,a)) = south p (q a) := by
  change meridian p (0,H (s,a)) = _
  rw [ray_zero,hH]

include hH in
lemma suspHomotopyRay_top (s : unitInterval) (a : A) :
    suspHomotopyRay H (s,(1,a)) = north p (q a) := by
  change meridian p (1,H (s,a)) = _
  rw [ray_one,hH]

def suspHomotopy : (suspMap f p q hf).Homotopy (suspMap g p q hg) where
  toContinuousMap := cylinderLift q q
    ((south p).comp ⟨Prod.snd,continuous_snd⟩) (suspHomotopyRay H)
    ((north p).comp ⟨Prod.snd,continuous_snd⟩)
    (suspHomotopyRay_bottom H hH) (suspHomotopyRay_top H hH)
  map_zero_left z := by
    induction z using induction with
    | hbase _ => rfl
    | hray ta =>
      change meridian p (ta.1,H (0,ta.2)) = meridian p (ta.1,f ta.2)
      rw [HomotopyLike.map_zero_left H]
    | hapex _ => rfl
  map_one_left z := by
    induction z using induction with
    | hbase _ => rfl
    | hray ta =>
      change meridian p (ta.1,H (1,ta.2)) = meridian p (ta.1,g ta.2)
      rw [HomotopyLike.map_one_left H]
    | hapex _ => rfl

lemma suspHomotopy_over (s : unitInterval) (z : Susp q) :
    suspProjection p (suspHomotopy hf hg H hH (s,z)) = suspProjection q z := by
  induction z using induction with
  | hbase _ => rfl
  | hray ta => exact hH s ta.2
  | hapex _ => rfl

end NearbyLagrangian.FiberCone

end

end OAI
