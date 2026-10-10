import Mathlib

namespace OAI

/-! Fiberwise cones, contractions and left suspension homotopies. -/

noncomputable section
universe u v w
open Set ContinuousMap
open scoped Topology unitInterval

namespace NearbyLagrangian.FiberCone

variable {B A X Y : Type*} [TopologicalSpace B] [TopologicalSpace A]
  [TopologicalSpace X] [TopologicalSpace Y]

abbrev Raw (B A X : Type*) := X ⊕ ((unitInterval × A) ⊕ B)

inductive Seam (f : C(A,X)) (q : C(A,B)) : Raw B A X → Raw B A X → Prop
  | bottom (a : A) : Seam f q (.inr (.inl (0,a))) (.inl (f a))
  | top (a : A) : Seam f q (.inr (.inl (1,a))) (.inr (.inr (q a)))

def Space (f : C(A,X)) (q : C(A,B)) := Quot (Seam f q)
instance (f : C(A,X)) (q : C(A,B)) : TopologicalSpace (Space f q) :=
  inferInstanceAs (TopologicalSpace (Quot (Seam f q)))

def base (f : C(A,X)) (q : C(A,B)) : C(X,Space f q) :=
  ⟨fun x => Quot.mk _ (.inl x),continuous_quot_mk.comp continuous_inl⟩
def ray (f : C(A,X)) (q : C(A,B)) : C(unitInterval × A,Space f q) :=
  ⟨fun z => Quot.mk _ (.inr (.inl z)),
    continuous_quot_mk.comp (continuous_inr.comp continuous_inl)⟩
def apex (f : C(A,X)) (q : C(A,B)) : C(B,Space f q) :=
  ⟨fun b => Quot.mk _ (.inr (.inr b)),
    continuous_quot_mk.comp (continuous_inr.comp continuous_inr)⟩

@[simp] lemma ray_zero (f : C(A,X)) (q : C(A,B)) (a : A) :
    ray f q (0,a) = base f q (f a) := Quot.sound (Seam.bottom a)
@[simp] lemma ray_one (f : C(A,X)) (q : C(A,B)) (a : A) :
    ray f q (1,a) = apex f q (q a) := Quot.sound (Seam.top a)

def lift (f : C(A,X)) (q : C(A,B)) (i : C(X,Y))
    (c : C(unitInterval × A,Y)) (v : C(B,Y))
    (h₀ : ∀ a, c (0,a) = i (f a)) (h₁ : ∀ a, c (1,a) = v (q a)) :
    C(Space f q,Y) where
  toFun := Quot.lift (Sum.elim i (Sum.elim c v)) (by
    intro a b h
    cases h with
    | bottom a => exact h₀ a
    | top a => exact h₁ a)
  continuous_toFun := continuous_quot_lift _
    (i.continuous.sumElim (c.continuous.sumElim v.continuous))

@[simp] lemma lift_base (f : C(A,X)) (q : C(A,B)) (i : C(X,Y))
    (c : C(unitInterval × A,Y)) (v : C(B,Y))
    (h₀ : ∀ a, c (0,a) = i (f a)) (h₁ : ∀ a, c (1,a) = v (q a)) (x : X) :
    lift f q i c v h₀ h₁ (base f q x) = i x := rfl
@[simp] lemma lift_ray (f : C(A,X)) (q : C(A,B)) (i : C(X,Y))
    (c : C(unitInterval × A,Y)) (v : C(B,Y))
    (h₀ : ∀ a, c (0,a) = i (f a)) (h₁ : ∀ a, c (1,a) = v (q a)) (z : unitInterval × A) :
    lift f q i c v h₀ h₁ (ray f q z) = c z := rfl
@[simp] lemma lift_apex (f : C(A,X)) (q : C(A,B)) (i : C(X,Y))
    (c : C(unitInterval × A,Y)) (v : C(B,Y))
    (h₀ : ∀ a, c (0,a) = i (f a)) (h₁ : ∀ a, c (1,a) = v (q a)) (b : B) :
    lift f q i c v h₀ h₁ (apex f q b) = v b := rfl

@[elab_as_elim] theorem induction {f : C(A,X)} {q : C(A,B)}
    {P : Space f q → Prop} (hbase : ∀ x, P (base f q x))
    (hray : ∀ ta, P (ray f q ta)) (hapex : ∀ b, P (apex f q b)) (z : Space f q) : P z := by
  induction z using Quot.inductionOn with
  | h z =>
    rcases z with x | (ta | b)
    · exact hbase x
    · exact hray ta
    · exact hapex b

def projection (f : C(A,X)) (p : C(X,B)) (q : C(A,B))
    (hf : ∀ a, p (f a) = q a) : C(Space f q,B) :=
  lift f q p (q.comp ⟨Prod.snd,continuous_snd⟩) (ContinuousMap.id B)
    (fun a => (hf a).symm) (fun _ => rfl)

@[simp] lemma projection_base (f : C(A,X)) (p : C(X,B)) (q : C(A,B))
    (hf : ∀ a, p (f a) = q a) (x : X) : projection f p q hf (base f q x) = p x := rfl
@[simp] lemma projection_ray (f : C(A,X)) (p : C(X,B)) (q : C(A,B))
    (hf : ∀ a, p (f a) = q a) (ta : unitInterval × A) :
    projection f p q hf (ray f q ta) = q ta.2 := rfl
@[simp] lemma projection_apex (f : C(A,X)) (p : C(X,B)) (q : C(A,B))
    (hf : ∀ a, p (f a) = q a) (b : B) : projection f p q hf (apex f q b) = b := rfl

abbrev Susp (q : C(A,B)) := Space q q

def suspProjection (q : C(A,B)) : C(Susp q,B) :=
  projection q (ContinuousMap.id B) q (fun _ => rfl)

abbrev south (q : C(A,B)) : C(B,Susp q) := base q q
abbrev meridian (q : C(A,B)) : C(unitInterval × A,Susp q) := ray q q
abbrev north (q : C(A,B)) : C(B,Susp q) := apex q q

def suspMap (f : C(A,X)) (p : C(X,B)) (q : C(A,B))
    (hf : ∀ a, p (f a) = q a) : C(Susp q,Susp p) :=
  lift q q (south p)
    ((meridian p).comp ⟨fun ta => (ta.1,f ta.2),continuous_fst.prodMk
      (f.continuous.comp continuous_snd)⟩) (north p)
    (fun a => by change meridian p (0,f a) = south p (q a); rw [ray_zero,hf])
    (fun a => by change meridian p (1,f a) = north p (q a); rw [ray_one,hf])

@[simp] lemma suspMap_south (f : C(A,X)) (p : C(X,B)) (q : C(A,B))
    (hf : ∀ a, p (f a) = q a) (b : B) : suspMap f p q hf (south q b) = south p b := rfl
@[simp] lemma suspMap_meridian (f : C(A,X)) (p : C(X,B)) (q : C(A,B))
    (hf : ∀ a, p (f a) = q a) (ta : unitInterval × A) :
    suspMap f p q hf (meridian q ta) = meridian p (ta.1,f ta.2) := rfl
@[simp] lemma suspMap_north (f : C(A,X)) (p : C(X,B)) (q : C(A,B))
    (hf : ∀ a, p (f a) = q a) (b : B) : suspMap f p q hf (north q b) = north p b := rfl

lemma suspMap_over (f : C(A,X)) (p : C(X,B)) (q : C(A,B))
    (hf : ∀ a, p (f a) = q a) (z : Susp q) :
    suspProjection p (suspMap f p q hf z) = suspProjection q z := by
  induction z using induction with
  | hbase b => rfl
  | hray ta => exact hf ta.2
  | hapex b => rfl

def collapse (f : C(A,X)) (p : C(X,B)) (q : C(A,B))
    (hf : ∀ a, p (f a) = q a) : C(Space f q,Susp q) :=
  lift f q ((south q).comp p) (meridian q) (north q)
    (fun a => by change meridian q (0,a) = south q (p (f a)); rw [ray_zero,hf])
    (fun a => ray_one q q a)

@[simp] lemma collapse_base (f : C(A,X)) (p : C(X,B)) (q : C(A,B))
    (hf : ∀ a, p (f a) = q a) (x : X) : collapse f p q hf (base f q x) = south q (p x) := rfl
@[simp] lemma collapse_ray (f : C(A,X)) (p : C(X,B)) (q : C(A,B))
    (hf : ∀ a, p (f a) = q a) (ta : unitInterval × A) : collapse f p q hf (ray f q ta) = meridian q ta := rfl
@[simp] lemma collapse_apex (f : C(A,X)) (p : C(X,B)) (q : C(A,B))
    (hf : ∀ a, p (f a) = q a) (b : B) : collapse f p q hf (apex f q b) = north q b := rfl

lemma collapse_over (f : C(A,X)) (p : C(X,B)) (q : C(A,B))
    (hf : ∀ a, p (f a) = q a) (z : Space f q) :
    suspProjection q (collapse f p q hf z) = projection f p q hf z := by
  induction z using induction with
  | hbase x => rfl
  | hray ta => rfl
  | hapex b => rfl

end NearbyLagrangian.FiberCone

end

noncomputable section
universe u v w
open Set ContinuousMap
open scoped Topology unitInterval

namespace NearbyLagrangian.FiberCone
variable {B A X : Type*} [TopologicalSpace B] [TopologicalSpace A] [TopologicalSpace X]

structure Contraction (f : C(A,X)) (p : C(X,B)) (q : C(A,B))
    (hf : ∀ a, p (f a) = q a) where
  hom : C(unitInterval × Space f q,Space f q)
  at_zero : ∀ z, hom (0,z) = z
  at_one : ∀ z, hom (1,z) = apex f q (projection f p q hf z)
  staysOver : ∀ t z, projection f p q hf (hom (t,z)) = projection f p q hf z
  fixed : ∀ t b, hom (t,apex f q b) = apex f q b

namespace Contraction
variable {f : C(A,X)} {p : C(X,B)} {q : C(A,B)} {hf : ∀ a, p (f a) = q a}
variable (H : Contraction f p q hf)

def inverseRay : C(unitInterval × X,Susp q) :=
  (collapse f p q hf).comp
    (H.hom.comp ⟨fun tx => (tx.1,base f q tx.2),
      continuous_fst.prodMk ((base f q).continuous.comp continuous_snd)⟩)

@[simp] lemma inverseRay_zero (x : X) : H.inverseRay (0,x) = south q (p x) := by
  change collapse f p q hf (H.hom (0,base f q x)) = _
  rw [H.at_zero,collapse_base]
@[simp] lemma inverseRay_one (x : X) : H.inverseRay (1,x) = north q (p x) := by
  change collapse f p q hf (H.hom (1,base f q x)) = _
  rw [H.at_one,projection_base,collapse_apex]

def inverse : C(Susp p,Susp q) :=
  lift p p (south q) H.inverseRay (north q) H.inverseRay_zero H.inverseRay_one

@[simp] lemma inverse_south (b : B) : H.inverse (south p b) = south q b := rfl
@[simp] lemma inverse_meridian (tx : unitInterval × X) :
    H.inverse (meridian p tx) = collapse f p q hf (H.hom (tx.1,base f q tx.2)) := rfl
@[simp] lemma inverse_north (b : B) : H.inverse (north p b) = north q b := rfl

lemma inverse_over (z : Susp p) : suspProjection q (H.inverse z) = suspProjection p z := by
  induction z using induction with
  | hbase b => rfl
  | hray tx =>
    rw [inverse_meridian,collapse_over,H.staysOver,projection_base]
    rfl
  | hapex b => rfl

end Contraction

def squareDen (s : unitInterval) : ℝ := max (s:ℝ) (1-(s:ℝ))
lemma squareDen_pos (s : unitInterval) : 0 < squareDen s := by
  have ha := le_max_left (s:ℝ) (1-(s:ℝ))
  have hb := le_max_right (s:ℝ) (1-(s:ℝ))
  dsimp [squareDen]
  linarith
lemma continuous_squareDen : Continuous squareDen :=
  continuous_subtype_val.max (continuous_const.sub continuous_subtype_val)

def horizontal : C(unitInterval × unitInterval,unitInterval) where
  toFun st := ⟨(1-(st.1:ℝ))*(st.2:ℝ) / squareDen st.1,by
    refine ⟨div_nonneg (mul_nonneg (sub_nonneg.mpr st.1.property.2) st.2.property.1)
      (squareDen_pos st.1).le,?_⟩
    apply (div_le_one (squareDen_pos st.1)).mpr
    have h := mul_le_mul_of_nonneg_left st.2.property.2 (sub_nonneg.mpr st.1.property.2)
    have h' : (1 - (st.1:ℝ)) * (st.2:ℝ) ≤ 1 - (st.1:ℝ) := by
      simpa only [mul_one] using h
    exact h'.trans (le_max_right _ _)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
    (continuous_subtype_val.comp continuous_snd)).div
      (continuous_squareDen.comp continuous_fst) (fun _ => (squareDen_pos _).ne'))

def vertical : C(unitInterval × unitInterval,unitInterval) where
  toFun st := ⟨(st.1:ℝ)*(st.2:ℝ) / squareDen st.1,by
    refine ⟨div_nonneg (mul_nonneg st.1.property.1 st.2.property.1) (squareDen_pos st.1).le,?_⟩
    apply (div_le_one (squareDen_pos st.1)).mpr
    have h := mul_le_mul_of_nonneg_left st.2.property.2 st.1.property.1
    have h' : (st.1:ℝ) * (st.2:ℝ) ≤ (st.1:ℝ) := by
      simpa only [mul_one] using h
    exact h'.trans (le_max_left _ _)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (((continuous_subtype_val.comp continuous_fst).mul
    (continuous_subtype_val.comp continuous_snd)).div
      (continuous_squareDen.comp continuous_fst) (fun _ => (squareDen_pos _).ne'))

@[simp] lemma horizontal_left (t : unitInterval) : horizontal (0,t) = t := by
  apply Subtype.ext
  simp [horizontal,squareDen]
@[simp] lemma horizontal_right (t : unitInterval) : horizontal (1,t) = 0 := by
  apply Subtype.ext
  simp [horizontal,squareDen]
@[simp] lemma vertical_left (t : unitInterval) : vertical (0,t) = 0 := by
  apply Subtype.ext
  simp [vertical,squareDen]
@[simp] lemma vertical_right (t : unitInterval) : vertical (1,t) = t := by
  apply Subtype.ext
  simp [vertical,squareDen]
@[simp] lemma horizontal_bottom (s : unitInterval) : horizontal (s,0) = 0 := by
  apply Subtype.ext
  simp [horizontal]
@[simp] lemma vertical_bottom (s : unitInterval) : vertical (s,0) = 0 := by
  apply Subtype.ext
  simp [vertical]

lemma square_top (s : unitInterval) : horizontal (s,1) = 1 ∨ vertical (s,1) = 1 := by
  rcases le_total (s:ℝ) (1-(s:ℝ)) with hs | hs
  · left
    apply Subtype.ext
    have hn : 1-(s:ℝ) ≠ 0 := by
      have hd := squareDen_pos s
      rw [squareDen,max_eq_right hs] at hd
      exact hd.ne'
    simp [horizontal,squareDen,max_eq_right hs,hn]
  · right
    apply Subtype.ext
    have hn : (s:ℝ) ≠ 0 := by
      have hd := squareDen_pos s
      rw [squareDen,max_eq_left hs] at hd
      exact hd.ne'
    simp [vertical,squareDen,max_eq_left hs,hn]

end NearbyLagrangian.FiberCone

end

noncomputable section
universe u v w
open Set ContinuousMap
open scoped Topology unitInterval

namespace NearbyLagrangian.FiberCone
variable {B A X Y : Type*} [TopologicalSpace B] [TopologicalSpace A]
  [TopologicalSpace X] [TopologicalSpace Y]

def cylinderLift (f : C(A,X)) (q : C(A,B)) (i : C(unitInterval × X,Y))
    (c : C(unitInterval × (unitInterval × A),Y)) (v : C(unitInterval × B,Y))
    (h₀ : ∀ s a, c (s,(0,a)) = i (s,f a))
    (h₁ : ∀ s a, c (s,(1,a)) = v (s,q a)) : C(unitInterval × Space f q,Y) :=
  (ContinuousMap.uncurry (lift f q
    (ContinuousMap.curry (i.comp ContinuousMap.prodSwap))
    (ContinuousMap.curry (c.comp ContinuousMap.prodSwap))
    (ContinuousMap.curry (v.comp ContinuousMap.prodSwap))
    (fun a => by ext s; exact h₀ s a)
    (fun a => by ext s; exact h₁ s a))).comp ContinuousMap.prodSwap

@[simp] lemma cylinderLift_base (f : C(A,X)) (q : C(A,B)) (i : C(unitInterval × X,Y))
    (c : C(unitInterval × (unitInterval × A),Y)) (v : C(unitInterval × B,Y))
    (h₀ : ∀ s a, c (s,(0,a)) = i (s,f a))
    (h₁ : ∀ s a, c (s,(1,a)) = v (s,q a)) (s : unitInterval) (x : X) :
    cylinderLift f q i c v h₀ h₁ (s,base f q x) = i (s,x) := rfl
@[simp] lemma cylinderLift_ray (f : C(A,X)) (q : C(A,B)) (i : C(unitInterval × X,Y))
    (c : C(unitInterval × (unitInterval × A),Y)) (v : C(unitInterval × B,Y))
    (h₀ : ∀ s a, c (s,(0,a)) = i (s,f a))
    (h₁ : ∀ s a, c (s,(1,a)) = v (s,q a)) (s : unitInterval) (ta : unitInterval × A) :
    cylinderLift f q i c v h₀ h₁ (s,ray f q ta) = c (s,ta) := rfl
@[simp] lemma cylinderLift_apex (f : C(A,X)) (q : C(A,B)) (i : C(unitInterval × X,Y))
    (c : C(unitInterval × (unitInterval × A),Y)) (v : C(unitInterval × B,Y))
    (h₀ : ∀ s a, c (s,(0,a)) = i (s,f a))
    (h₁ : ∀ s a, c (s,(1,a)) = v (s,q a)) (s : unitInterval) (b : B) :
    cylinderLift f q i c v h₀ h₁ (s,apex f q b) = v (s,b) := rfl

namespace Contraction
variable {f : C(A,X)} {p : C(X,B)} {q : C(A,B)} {hf : ∀ a, p (f a) = q a}
variable (H : Contraction f p q hf)

def leftRay : C(unitInterval × (unitInterval × A),Susp q) where
  toFun z := collapse f p q hf (H.hom
    (vertical (z.1,z.2.1),ray f q (horizontal (z.1,z.2.1),z.2.2)))
  continuous_toFun := (collapse f p q hf).continuous.comp (H.hom.continuous.comp
    ((vertical.continuous.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk
      ((ray f q).continuous.comp
        ((horizontal.continuous.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk
          (continuous_snd.comp continuous_snd)))))

lemma leftRay_bottom (s : unitInterval) (a : A) : H.leftRay (s,(0,a)) = south q (q a) := by
  change collapse f p q hf (H.hom (vertical (s,0),ray f q (horizontal (s,0),a))) = _
  rw [horizontal_bottom,vertical_bottom,H.at_zero,ray_zero,collapse_base,hf]

lemma leftRay_top (s : unitInterval) (a : A) : H.leftRay (s,(1,a)) = north q (q a) := by
  change collapse f p q hf (H.hom (vertical (s,1),ray f q (horizontal (s,1),a))) = _
  rcases square_top s with hx | hy
  · rw [hx,ray_one,H.fixed,collapse_apex]
  · rw [hy,H.at_one,projection_ray,collapse_apex]

def leftDeformation : C(unitInterval × Susp q,Susp q) :=
  cylinderLift q q ((south q).comp ⟨Prod.snd,continuous_snd⟩) H.leftRay
    ((north q).comp ⟨Prod.snd,continuous_snd⟩) H.leftRay_bottom H.leftRay_top

@[simp] lemma leftDeformation_south (s : unitInterval) (b : B) :
    H.leftDeformation (s,south q b) = south q b := rfl
@[simp] lemma leftDeformation_meridian (s : unitInterval) (ta : unitInterval × A) :
    H.leftDeformation (s,meridian q ta) = H.leftRay (s,ta) := rfl
@[simp] lemma leftDeformation_north (s : unitInterval) (b : B) :
    H.leftDeformation (s,north q b) = north q b := rfl

lemma leftDeformation_zero (z : Susp q) : H.leftDeformation (0,z) = z := by
  induction z using induction with
  | hbase b => rfl
  | hray ta =>
    rw [leftDeformation_meridian]
    change collapse f p q hf (H.hom
      (vertical (0,ta.1),ray f q (horizontal (0,ta.1),ta.2))) = _
    rw [horizontal_left,vertical_left,H.at_zero,collapse_ray]
  | hapex b => rfl

lemma leftDeformation_one (z : Susp q) :
    H.leftDeformation (1,z) = H.inverse (suspMap f p q hf z) := by
  induction z using induction with
  | hbase b => rw [leftDeformation_south,suspMap_south,inverse_south]
  | hray ta =>
    rw [leftDeformation_meridian,suspMap_meridian,inverse_meridian]
    change collapse f p q hf (H.hom
      (vertical (1,ta.1),ray f q (horizontal (1,ta.1),ta.2))) = _
    rw [horizontal_right,vertical_right,ray_zero]
  | hapex b => rw [leftDeformation_north,suspMap_north,inverse_north]

lemma leftDeformation_over (s : unitInterval) (z : Susp q) :
    suspProjection q (H.leftDeformation (s,z)) = suspProjection q z := by
  induction z using induction with
  | hbase b => rfl
  | hray ta =>
    rw [leftDeformation_meridian]
    change suspProjection q (collapse f p q hf (H.hom
      (vertical (s,ta.1),ray f q (horizontal (s,ta.1),ta.2)))) = _
    rw [collapse_over,H.staysOver,projection_ray]
    rfl
  | hapex b => rfl

def leftHomotopy : (H.inverse.comp (suspMap f p q hf)).Homotopy (ContinuousMap.id (Susp q)) :=
  ContinuousMap.Homotopy.symm
    { toContinuousMap := H.leftDeformation
      map_zero_left := H.leftDeformation_zero
      map_one_left := H.leftDeformation_one }

lemma leftHomotopy_over (s : unitInterval) (z : Susp q) :
    suspProjection q (H.leftHomotopy (s,z)) = suspProjection q z :=
  H.leftDeformation_over (unitInterval.symm s) z

end Contraction
end NearbyLagrangian.FiberCone

end

end OAI
