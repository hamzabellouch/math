import Mathlib
import OAI.Topology.Homotopy.CubicalNullity
import OAI.Topology.Homotopy.OpenCollapse

namespace OAI

/-! Cubical and spherical representatives of homotopy classes. -/

noncomputable section
universe u v w
open Set ContinuousMap Topology
open scoped OnePoint Topology Topology.Homotopy

namespace NearbyLagrangian.CubicalSphere
variable (N : Type*) [Fintype N] [Nonempty N]

def interiorCube : Set (N → unitInterval) := {t | ∀ i, 0 < (t i:ℝ) ∧ (t i:ℝ) < 1}
omit [Fintype N] [Nonempty N] in
lemma interiorCube_eq : interiorCube N = (Cube.boundary N)ᶜ := by
  ext t
  simp only [interiorCube,mem_ofPred_eq,Set.mem_compl_iff,Cube.boundary,not_exists,not_or]
  constructor
  · intro ht i
    constructor
    · intro h; have := (ht i).1; simp [h] at this
    · intro h; have := (ht i).2; simp [h] at this
  · intro ht i
    constructor
    · exact lt_of_le_of_ne (t i).property.1 (fun h => (ht i).1 (Subtype.ext h.symm))
    · exact lt_of_le_of_ne (t i).property.2 (fun h => (ht i).2 (Subtype.ext h))

omit [Nonempty N] in
lemma isOpen_interiorCube : IsOpen (interiorCube N) := by
  have he : interiorCube N = ⋂ i, {t : N → unitInterval | 0 < (t i:ℝ) ∧ (t i:ℝ) < 1} := by
    ext t; simp [interiorCube]
  rw [he]
  apply isOpen_iInter_of_finite
  intro i
  exact isOpen_Ioo.preimage (continuous_subtype_val.comp (continuous_apply i))

omit [Fintype N] in
lemma complement_nonempty : (interiorCube N)ᶜ.Nonempty := by
  refine ⟨fun _ => 0,?_⟩
  rw [interiorCube_eq,compl_compl]
  exact ⟨Classical.choice inferInstance,Or.inl rfl⟩

def interiorHomeomorph : interiorCube N ≃ₜ (N → Ioo (0:ℝ) 1) where
  toFun t i := ⟨t.1 i,(t.property i)⟩
  invFun t := ⟨fun i => ⟨(t i:ℝ),(t i).property.1.le,(t i).property.2.le⟩,
    fun i => (t i).property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    apply continuous_pi
    intro i
    exact (continuous_subtype_val.comp ((continuous_apply i).comp continuous_subtype_val)).subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    exact (continuous_subtype_val.comp (continuous_apply i)).subtype_mk _

def intervalHomeomorph : Ioo (0:ℝ) 1 ≃ₜ Ioo (-1:ℝ) 1 where
  toFun x := ⟨2*(x:ℝ)-1,by have h := x.property; constructor <;> linarith [h.1,h.2]⟩
  invFun y := ⟨((y:ℝ)+1)/2,by have h := y.property; constructor <;> linarith [h.1,h.2]⟩
  left_inv x := Subtype.ext (by dsimp; ring)
  right_inv y := Subtype.ext (by dsimp; ring)
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_const.mul continuous_subtype_val).sub continuous_const
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.add continuous_const).div_const 2

def interiorEuclidean : interiorCube N ≃ₜ (N → ℝ) :=
  (interiorHomeomorph N).trans (Homeomorph.piCongrRight fun _ =>
    intervalHomeomorph.trans (orderIsoIooNegOneOne ℝ).toHomeomorph.symm)

def compactificationSphere (n : ℕ) : OnePoint (interiorCube (Fin (n+1))) ≃ₜ
    Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+2))) 1 :=
  (interiorEuclidean (Fin (n+1))).onePointCongr.trans
    (onePointEquivSphereOfFinrankEq (by simp))

def spherePoint (n : ℕ) : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+2))) 1 :=
  compactificationSphere n ∞

def sphereQuotient (n : ℕ) : C((Fin (n+1) → unitInterval),
    Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+2))) 1) :=
  ⟨fun t => compactificationSphere n (OpenCollapse.collapse (interiorCube _) t),
    (compactificationSphere n).continuous.comp
      (OpenCollapse.continuous_collapse (isOpen_interiorCube _))⟩

lemma sphereQuotient_boundary (n : ℕ) {t : Fin (n+1) → unitInterval}
    (ht : t ∈ Cube.boundary _) : sphereQuotient n t = spherePoint n := by
  change compactificationSphere n _ = compactificationSphere n ∞
  rw [OpenCollapse.collapse_of_notMem]
  simpa only [interiorCube_eq,mem_compl_iff,not_not] using ht

lemma sphereQuotient_surjective (n : ℕ) : Function.Surjective (sphereQuotient n) :=
  (compactificationSphere n).surjective.comp
    (OpenCollapse.collapse_surjective (complement_nonempty _))

variable {X : Type*} [TopologicalSpace X] {x : X}

def sphereMap {n : ℕ} (f : GenLoop (Fin (n+1)) X x) :
    C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+2))) 1,X) :=
  (OpenCollapse.descend (isOpen_interiorCube _) (complement_nonempty _) f.1 x
      (fun t ht => GenLoop.boundary f t (by simpa only [interiorCube_eq,mem_compl_iff,not_not] using ht))).comp
    ⟨(compactificationSphere n).symm,(compactificationSphere n).symm.continuous⟩

@[simp] lemma sphereMap_quotient {n : ℕ} (f : GenLoop (Fin (n+1)) X x)
    (t : Fin (n+1) → unitInterval) : sphereMap f (sphereQuotient n t) = f t := by
  simp only [sphereMap,ContinuousMap.comp_apply,ContinuousMap.coe_mk,sphereQuotient,
    Homeomorph.symm_apply_apply,OpenCollapse.descend_collapse]
  rfl

@[simp] lemma sphereMap_point {n : ℕ} (f : GenLoop (Fin (n+1)) X x) :
    sphereMap f (spherePoint n) = x := by
  simp only [sphereMap,ContinuousMap.comp_apply,ContinuousMap.coe_mk,spherePoint,
    Homeomorph.symm_apply_apply]
  rfl

theorem sphereMap_null_implies_cube_null {n : ℕ} (f : GenLoop (Fin (n+1)) X x)
    (hf : (sphereMap f).Nullhomotopic) : GenLoop.Homotopic f GenLoop.const := by
  obtain ⟨y,⟨H⟩⟩ := hf
  let H' : f.1.Homotopy (ContinuousMap.const _ y) := {
    toFun := fun q => H (q.1,sphereQuotient n q.2)
    continuous_toFun := H.continuous.comp (continuous_fst.prodMk ((sphereQuotient n).continuous.comp continuous_snd))
    map_zero_left := fun t => (H.apply_zero _).trans (sphereMap_quotient f t)
    map_one_left := fun t => H.apply_one _ }
  let p : C(unitInterval,X) :=
    ⟨fun s => H (s,spherePoint n),H.continuous.comp (continuous_id.prodMk continuous_const)⟩
  apply CubicalFreeNullity.null_of_moving_base f H' p
  intro s t ht
  change H (s,sphereQuotient n t) = H (s,spherePoint n)
  rw [sphereQuotient_boundary n ht]

theorem sphereMap_null_implies_class_one {n : ℕ} (f : GenLoop (Fin (n+1)) X x)
    (hf : (sphereMap f).Nullhomotopic) :
    (⟦f⟧ : HomotopyGroup.Pi (n+1) X x) = (1 : HomotopyGroup.Pi (n+1) X x) := by
  rw [HomotopyGroup.one_def]
  exact Quotient.sound (sphereMap_null_implies_cube_null f hf)

end NearbyLagrangian.CubicalSphere

end

noncomputable section
universe u v w
open Set ContinuousMap Topology
open scoped OnePoint Topology Topology.Homotopy

namespace NearbyLagrangian.CubicalSphere
variable {X : Type*} [TopologicalSpace X] {x : X}

def sphereHomotopy {n : ℕ} {f g : GenLoop (Fin (n+1)) X x}
    (H : f.1.HomotopyRel g.1 (Cube.boundary _)) : (sphereMap f).Homotopy (sphereMap g) where
  toFun := fun q => ((compactificationSphere n).symm q.2).elim x
    (fun t => H (q.1,t))
  continuous_toFun := by
    let F : C(unitInterval × (Fin (n+1) → unitInterval),X) := ⟨H,H.continuous⟩
    have hF : ∀ s t, t ∉ interiorCube (Fin (n+1)) → F (s,t) = x := by
      intro s t ht
      have ht' : t ∈ Cube.boundary _ := by
        simpa only [interiorCube_eq,mem_compl_iff,not_not] using ht
      exact (H.eq_fst s ht').trans (GenLoop.boundary f t ht')
    exact (OpenCollapse.continuous_descend_param (isOpen_interiorCube _) (complement_nonempty _)
      F (const _ x) hF).comp (continuous_fst.prodMk
        ((compactificationSphere n).symm.continuous.comp continuous_snd))
  map_zero_left := by
    intro u
    change ((compactificationSphere n).symm u).elim x (fun t => H (0,t)) =
      ((compactificationSphere n).symm u).elim x (fun t => f t)
    generalize (compactificationSphere n).symm u = z
    induction z using OnePoint.rec with
    | infty => rfl
    | coe t => exact H.apply_zero t
  map_one_left := by
    intro u
    change ((compactificationSphere n).symm u).elim x (fun t => H (1,t)) =
      ((compactificationSphere n).symm u).elim x (fun t => g t)
    generalize (compactificationSphere n).symm u = z
    induction z using OnePoint.rec with
    | infty => rfl
    | coe t => exact H.apply_one t

@[simp] theorem sphereMap_const (n : ℕ) : sphereMap (GenLoop.const : GenLoop (Fin (n+1)) X x) =
    ContinuousMap.const _ x := by
  ext u
  obtain ⟨t,rfl⟩ := sphereQuotient_surjective n u
  exact sphereMap_quotient GenLoop.const t

theorem sphereMap_null_iff_cube_null {n : ℕ} (f : GenLoop (Fin (n+1)) X x) :
    (sphereMap f).Nullhomotopic ↔ GenLoop.Homotopic f GenLoop.const := by
  constructor
  · exact sphereMap_null_implies_cube_null f
  · rintro ⟨H⟩
    refine ⟨x,?_⟩
    rw [← sphereMap_const]
    exact ⟨sphereHomotopy H⟩

theorem sphereMap_null_iff_class_one {n : ℕ} (f : GenLoop (Fin (n+1)) X x) :
    (sphereMap f).Nullhomotopic ↔
      (⟦f⟧ : HomotopyGroup.Pi (n+1) X x) = (1 : HomotopyGroup.Pi (n+1) X x) := by
  rw [sphereMap_null_iff_cube_null,HomotopyGroup.one_def,Quotient.eq]
  rfl

end NearbyLagrangian.CubicalSphere

end

noncomputable section
universe u v w


namespace NearbyLagrangian.SphereConnectivity
open scoped Topology Topology.Homotopy

def genLoopMap {N A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (e : C(A,B)) {x : A} (f : GenLoop N A x) : GenLoop N B (e x) :=
  ⟨e.comp f.1,fun t ht => congrArg e (GenLoop.boundary f t ht)⟩
lemma genLoopMap_homotopic {N A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (e : C(A,B)) {x : A} {f g : GenLoop N A x} (h : GenLoop.Homotopic f g) :
    GenLoop.Homotopic (genLoopMap e f) (genLoopMap e g) := by
  obtain ⟨H⟩ := h
  exact ⟨H.compContinuousMap e⟩
def homotopyGroupMap {n : ℕ} {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (e : C(A,B)) (x : A) : HomotopyGroup.Pi n A x → HomotopyGroup.Pi n B (e x) :=
  Quotient.map (genLoopMap e) (fun _ _ h => genLoopMap_homotopic e h)
end NearbyLagrangian.SphereConnectivity

end

noncomputable section
universe u v w


namespace NearbyLagrangian.CubicalSphere
open Set ContinuousMap SphereConnectivity
open scoped Topology Topology.Homotopy
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x : X}

def sphereLoop {n : ℕ}
    (a : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+2))) 1,X)) :
    GenLoop (Fin (n+1)) X (a (spherePoint n)) :=
  ⟨a.comp (sphereQuotient n),fun _t ht => congrArg a (sphereQuotient_boundary n ht)⟩

@[simp] theorem sphereMap_sphereLoop {n : ℕ}
    (a : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+2))) 1,X)) :
    sphereMap (sphereLoop a) = a := by
  ext u
  obtain ⟨t,rfl⟩ := sphereQuotient_surjective n u
  rw [sphereMap_quotient]
  rfl

@[simp] theorem sphereMap_natural {n : ℕ} (e : C(X,Y))
    (f : GenLoop (Fin (n+1)) X x) :
    sphereMap (genLoopMap e f) = e.comp (sphereMap f) := by
  ext u
  obtain ⟨t,rfl⟩ := sphereQuotient_surjective n u
  rw [sphereMap_quotient,ContinuousMap.comp_apply,sphereMap_quotient]
  rfl

theorem null_iff_class_one {n : ℕ}
    (a : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+2))) 1,X)) :
    a.Nullhomotopic ↔
      (⟦sphereLoop a⟧ : HomotopyGroup.Pi (n+1) X (a (spherePoint n))) =
        (1 : HomotopyGroup.Pi (n+1) X (a (spherePoint n))) := by
  simpa only [sphereMap_sphereLoop] using sphereMap_null_iff_class_one (sphereLoop a)

theorem comp_null_iff_mapped_class_one {n : ℕ} (e : C(X,Y))
    (a : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+2))) 1,X)) :
    (e.comp a).Nullhomotopic ↔
      homotopyGroupMap (n:=n+1) e (a (spherePoint n)) ⟦sphereLoop a⟧ =
        (1 : HomotopyGroup.Pi (n+1) Y (e (a (spherePoint n)))) := by
  change (e.comp a).Nullhomotopic ↔
    (⟦genLoopMap e (sphereLoop a)⟧ : HomotopyGroup.Pi (n+1) Y (e (a (spherePoint n)))) = _
  simpa only [sphereMap_natural,sphereMap_sphereLoop] using
    sphereMap_null_iff_class_one (genLoopMap e (sphereLoop a))

end NearbyLagrangian.CubicalSphere

end

noncomputable section
universe u v w
open scoped Classical Topology Topology.Homotopy

namespace NearbyLagrangian.CubicalSphere
open Set ContinuousMap
open scoped OnePoint
variable {X : Type*} [TopologicalSpace X] {x y : X}

def sphereMovingHomotopy {n : ℕ} {f : GenLoop (Fin (n+1)) X x}
    {g : GenLoop (Fin (n+1)) X y} (H : f.1.Homotopy g.1)
    (p : Path x y) (hp : ∀ s t, t ∈ Cube.boundary (Fin (n+1)) → H (s,t) = p s) :
    (sphereMap f).Homotopy (sphereMap g) where
  toFun q := ((compactificationSphere n).symm q.2).elim (p q.1) (fun t => H (q.1,t))
  continuous_toFun := by
    let F : C(unitInterval × (Fin (n+1) → unitInterval),X) := ⟨H,H.continuous⟩
    have hF (s : unitInterval) (t : Fin (n+1) → unitInterval)
        (ht : t ∉ interiorCube (Fin (n+1))) : F (s,t) = p s := by
      apply hp
      simpa only [interiorCube_eq,mem_compl_iff,not_not] using ht
    exact (OpenCollapse.continuous_descend_param (isOpen_interiorCube _) (complement_nonempty _)
      F p.toContinuousMap hF).comp (continuous_fst.prodMk
        ((compactificationSphere n).symm.continuous.comp continuous_snd))
  map_zero_left := by
    intro u
    change ((compactificationSphere n).symm u).elim (p 0) (fun t => H (0,t)) =
      ((compactificationSphere n).symm u).elim x (fun t => f t)
    rw [p.source]
    generalize (compactificationSphere n).symm u = z
    induction z using OnePoint.rec with
    | infty => rfl
    | coe t => exact H.apply_zero t
  map_one_left := by
    intro u
    change ((compactificationSphere n).symm u).elim (p 1) (fun t => H (1,t)) =
      ((compactificationSphere n).symm u).elim y (fun t => g t)
    rw [p.target]
    generalize (compactificationSphere n).symm u = z
    induction z using OnePoint.rec with
    | infty => rfl
    | coe t => exact H.apply_one t

theorem exists_based_representative [PathConnectedSpace X] {n : ℕ}
    (a : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+2))) 1,X)) (x : X) :
    ∃ f : GenLoop (Fin (n+1)) X x, a.Homotopic (sphereMap f) := by
  obtain ⟨p⟩ := PathConnectedSpace.joined (a (spherePoint n)) x
  refine ⟨CubicalFreeNullity.rebase (sphereLoop a) p,?_⟩
  have h := sphereMovingHomotopy (CubicalFreeNullity.rebaseHomotopy (sphereLoop a) p) p
    (fun s _t ht => CubicalFreeNullity.rebaseValue_boundary (sphereLoop a) p s ht)
  simpa only [sphereMap_sphereLoop] using (show (sphereMap (sphereLoop a)).Homotopic
    (sphereMap (CubicalFreeNullity.rebase (sphereLoop a) p)) from ⟨h⟩)

end NearbyLagrangian.CubicalSphere

end

end OAI
