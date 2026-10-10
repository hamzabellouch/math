import Mathlib

namespace OAI

/-! Continuous collapse to a one-point compactification and parameterized descent. -/

noncomputable section
universe u v w
open Set ContinuousMap Topology
open scoped Classical OnePoint Topology

namespace NearbyLagrangian.OpenCollapse
variable {Y : Type*}

def collapse (U : Set Y) (y : Y) : OnePoint U :=
  if h : y ∈ U then (⟨y,h⟩ : U) else ∞

@[simp] lemma collapse_of_mem {U : Set Y} {y : Y} (h : y ∈ U) :
    collapse U y = (⟨y,h⟩ : U) := by simp [collapse,h]
@[simp] lemma collapse_of_notMem {U : Set Y} {y : Y} (h : y ∉ U) :
    collapse U y = ∞ := by simp [collapse,h]
lemma collapse_eq_infty {U : Set Y} {y : Y} : collapse U y = ∞ ↔ y ∉ U := by
  by_cases h : y ∈ U <;> simp [h]
lemma collapse_eq {U : Set Y} {y z : Y} :
    collapse U y = collapse U z ↔ y = z ∨ y ∉ U ∧ z ∉ U := by
  by_cases hy : y ∈ U
  · by_cases hz : z ∈ U
    · simp [collapse,hy,hz]
    · have hn : y ≠ z := by rintro rfl; contradiction
      simp [collapse,hy,hz,hn]
  · by_cases hz : z ∈ U
    · have hn : y ≠ z := by rintro rfl; contradiction
      simp [collapse,hy,hz,hn]
    · simp [collapse,hy,hz]

variable [TopologicalSpace Y] [T2Space Y]

lemma continuous_collapse {U : Set Y} (hU : IsOpen U) : Continuous (collapse U) := by
  rw [continuous_def]
  intro S hS
  by_cases hi : ∞ ∈ S
  · have hK := ((OnePoint.isOpen_iff_of_mem hi).mp hS).2
    have he : (collapse U ⁻¹' S)ᶜ = Subtype.val '' (((↑) : U → OnePoint U) ⁻¹' S)ᶜ := by
      ext y
      by_cases hy : y ∈ U
      · simp [hy,Set.mem_image,collapse]
      · simp [hy,collapse,hi]
    rw [← isClosed_compl_iff,he]
    exact (hK.image continuous_subtype_val).isClosed
  · have hV := (OnePoint.isOpen_iff_of_notMem hi).mp hS
    have he : collapse U ⁻¹' S = Subtype.val '' (((↑) : U → OnePoint U) ⁻¹' S) := by
      ext y
      by_cases hy : y ∈ U
      · simp [hy,Set.mem_image,collapse]
      · simp [hy,collapse,hi]
    rw [he]
    exact hU.isOpenMap_subtype_val _ hV

omit [TopologicalSpace Y] [T2Space Y] in
lemma collapse_surjective {U : Set Y} (hU : Uᶜ.Nonempty) : Function.Surjective (collapse U) := by
  intro z
  induction z using OnePoint.rec with
  | infty => obtain ⟨y,hy⟩ := hU; exact ⟨y,collapse_of_notMem hy⟩
  | coe y => exact ⟨y,collapse_of_mem y.property⟩

variable [CompactSpace Y]
lemma isQuotientMap_collapse {U : Set Y} (hU : IsOpen U) (hUc : Uᶜ.Nonempty) :
    IsQuotientMap (collapse U) := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  exact (continuous_collapse hU).isClosedMap.isQuotientMap (continuous_collapse hU)
    (collapse_surjective hUc)

def descend {U : Set Y} (hU : IsOpen U) (hUc : Uᶜ.Nonempty)
    {X : Type*} [TopologicalSpace X] (f : C(Y,X)) (x : X)
    (hf : ∀ y ∉ U, f y = x) : C(OnePoint U,X) where
  toFun := fun z => z.elim x (fun y => f y)
  continuous_toFun := (isQuotientMap_collapse hU hUc).continuous_iff.mpr (by
    have he : (fun z : OnePoint U => z.elim x (fun y => f y)) ∘ collapse U = f := by
      funext y
      by_cases hy : y ∈ U
      · simp [hy]
      · simp [hy,hf y hy]
    rw [he]
    exact f.continuous)

@[simp] lemma descend_collapse {U : Set Y} (hU : IsOpen U) (hUc : Uᶜ.Nonempty)
    {X : Type*} [TopologicalSpace X] (f : C(Y,X)) (x : X)
    (hf : ∀ y ∉ U, f y = x) (y : Y) : descend hU hUc f x hf (collapse U y) = f y := by
  by_cases hy : y ∈ U <;> simp [descend,hy,hf y]

end NearbyLagrangian.OpenCollapse

end

noncomputable section
universe u v w
open Set ContinuousMap Topology
open scoped Classical OnePoint Topology

namespace NearbyLagrangian.OpenCollapse
variable {Y P X : Type*} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
  [TopologicalSpace P] [T2Space P] [CompactSpace P] [TopologicalSpace X]

lemma continuous_descend_param {U : Set Y} (hU : IsOpen U) (hUc : Uᶜ.Nonempty)
    (F : C(P × Y,X)) (g : C(P,X)) (hF : ∀ p y, y ∉ U → F (p,y) = g p) :
    Continuous (fun q : P × OnePoint U => q.2.elim (g q.1) (fun y => F (q.1,y))) := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let c : P × Y → P × OnePoint U := fun z => (z.1,collapse U z.2)
  have hc : Continuous c := continuous_fst.prodMk ((continuous_collapse hU).comp continuous_snd)
  have hs : Function.Surjective c := by
    rintro ⟨p,z⟩
    obtain ⟨y,hy⟩ := collapse_surjective hUc z
    exact ⟨(p,y),Prod.ext rfl hy⟩
  have hq := hc.isClosedMap.isQuotientMap hc hs
  apply hq.continuous_iff.mpr
  have he : (fun q : P × OnePoint U => q.2.elim (g q.1) (fun y => F (q.1,y))) ∘ c = F := by
    funext q
    rcases q with ⟨p,y⟩
    change (collapse U y).elim (g p) (fun y => F (p,y)) = F (p,y)
    by_cases hy : y ∈ U <;> simp [hy,hF p y]
  rw [he]
  exact F.continuous

end NearbyLagrangian.OpenCollapse

end

end OAI
