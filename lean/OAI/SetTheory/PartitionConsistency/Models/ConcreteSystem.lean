import Mathlib
import OAI.SetTheory.PartitionConsistency.Models.ComponentGluing
import OAI.SetTheory.PartitionConsistency.Construction.SaturatedMonoids
import OAI.SetTheory.PartitionConsistency.Forcing.ChoiceFailure

namespace OAI

/-! ## CardinalParameters -/

namespace PartitionConsistency.CardinalParameters
noncomputable section
open Cardinal

/-- Every countable sequence below a regular uncountable initial ordinal is
strictly bounded. We use the small representative of that ordinal. -/
theorem countable_bound {μ : Cardinal.{0}} (hμ : μ.IsRegular) (hω : aleph0 < μ)
    (f : ℕ → μ.ord.ToType) : ∃ a : μ.ord.ToType, ∀ n, f n < a := by
  let g : ℕ → Ordinal := fun n => (f n).toOrd.val
  have hg : (⨆ n, g n + 1) < μ.ord :=
    Ordinal.iSup_add_one_lt_of_lt_cof
      (by simpa only [Cardinal.mk_nat,hμ.cof_ord] using hω)
      (fun n => (f n).toOrd.property)
  refine ⟨Ordinal.ToType.mk ⟨_,hg⟩,fun n => ?_⟩
  apply Ordinal.ToType.mk.symm.strictMono.lt_iff_lt.mp
  change (f n).toOrd < Ordinal.ToType.mk.symm (Ordinal.ToType.mk ⟨_,hg⟩)
  rw [OrderIso.symm_apply_apply]
  exact Ordinal.lt_iSup_add_one g n

/-- The cardinal arithmetic used in the paper for a successor of a fixed
point of countable exponentiation. This is not an inaccessible assumption. -/
theorem succ_power_aleph0 {c : Cardinal.{0}} (hω : aleph0 ≤ c)
    (hc : c ^ aleph0 = c) : (Order.succ c) ^ aleph0 = Order.succ c := by
  let μ := Order.succ c
  let A := μ.ord.ToType
  have hreg : μ.IsRegular := Cardinal.isRegular_succ hω
  have hωμ : aleph0 < μ := hω.trans_lt (Order.lt_succ c)
  have hbound (f : ℕ → A) : ∃ a : A, ∀ n, f n < a := countable_bound hreg hωμ f
  let bound : (ℕ → A) → A := fun f => (hbound f).choose
  let pack : (ℕ → A) → Σ a : A, (ℕ → Set.Iio a) :=
    fun f => ⟨bound f,fun n => ⟨f n,(hbound f).choose_spec n⟩⟩
  have hpack : Function.Injective pack := by
    intro f g h
    exact congrArg (fun t : Σ a : A, (ℕ → Set.Iio a) => fun n => (t.2 n).val) h
  have hfiber (a : A) : Cardinal.mk (ℕ → Set.Iio a) ≤ c := by
    have ha : Cardinal.mk (Set.Iio a) ≤ c := by
      apply (Order.lt_succ_iff).mp
      simpa [A,μ] using Cardinal.mk_Iio_lt a (by simp [A,μ])
    simpa only [Cardinal.mk_arrow,Cardinal.mk_nat,Cardinal.lift_id,hc] using
      Cardinal.power_le_power_right (c := aleph0) ha
  apply le_antisymm _ (Cardinal.self_le_power μ Cardinal.one_le_aleph0)
  calc
    μ ^ aleph0 = Cardinal.mk (ℕ → A) := by simp [A]
    _ ≤ Cardinal.mk (Σ a : A, ℕ → Set.Iio a) := Cardinal.mk_le_of_injective hpack
    _ = Cardinal.sum (fun a : A => Cardinal.mk (ℕ → Set.Iio a)) := Cardinal.mk_sigma _
    _ ≤ Cardinal.sum (fun _ : A => c) := Cardinal.sum_le_sum _ _ hfiber
    _ = μ * c := by simp [A]
    _ ≤ μ * μ := mul_le_mul_right (Order.le_succ c) μ
    _ = μ := Cardinal.mul_eq_self hωμ.le

/-- The parameters of RC262 over the ambient choice ground. -/
def μ : Cardinal.{0} := Order.succ Cardinal.continuum

theorem aleph_one_le_μ : Cardinal.aleph 1 ≤ μ :=
  Cardinal.aleph_one_le_continuum.trans (Order.le_succ _)

theorem aleph0_le_μ : Cardinal.aleph0 ≤ μ :=
  Cardinal.aleph0_le_continuum.trans (Order.le_succ _)

theorem μ_countable_power : μ ^ Cardinal.aleph0 = μ :=
  succ_power_aleph0 Cardinal.aleph0_le_continuum Cardinal.continuum_power_aleph0

theorem μ_regular : μ.IsRegular := Cardinal.isRegular_succ Cardinal.aleph0_le_continuum

end
end PartitionConsistency.CardinalParameters


/-! ## Instance -/

namespace PartitionConsistency.ConcreteSystem
open MonoidConstruction CardinalParameters DiagramForcing SetForcingNames
noncomputable section

/-- A small type of precisely the source's probe multiplicity. -/
abbrev K : Type := μ.ord.ToType
instance : Nonempty K := Ordinal.nonempty_toType_iff.mpr μ_regular.ord_pos.ne'

@[simp] theorem cardinal_K : Cardinal.mk K = μ := by
  rw [K,Cardinal.mk_toType,Cardinal.card_ord]

/-- The fully executed, omega-one-length saturation. -/
def T : Object := Saturation.target Base.object K

private theorem base_cardinal_le : Cardinal.mk Base.object ≤ μ := by
  change Cardinal.mk (Multiplicative ℕ) ≤ μ
  simpa using aleph0_le_μ

@[simp] theorem cardinal_T : Cardinal.mk T = μ :=
  Saturation.target_cardinal Base.object K aleph_one_le_μ μ_countable_power
    base_cardinal_le cardinal_K

instance : Infinite T := Cardinal.aleph0_le_mk_iff.mp (by rw [cardinal_T]; exact aleph0_le_μ)

theorem finiteMergers : HasFiniteMergers T := Saturation.finiteMergers Base.object K

theorem complement_cardinal :
    Cardinal.mk ((Set.range (fun x : T => T.e * x))ᶜ : Set T) = Cardinal.mk T := by
  have hh : (Set.range (fun x : T => T.e * x))ᶜ = {x : T | ¬ T.e ∣ x} := by
    ext x
    simp only [Set.mem_compl_iff,Set.mem_range,Set.mem_ofPred_eq,dvd_def]
    simp only [eq_comm]
  rw [hh,cardinal_T]
  exact Saturation.complement_cardinal Base.object K aleph_one_le_μ μ_countable_power
    base_cardinal_le cardinal_K

/-- The coordinates and Cohen length specified in the source. -/
abbrev I : Type := (Order.succ μ).ord.ToType
abbrev κ : Type := (Cardinal.aleph 1).ord.ToType

@[simp] theorem cardinal_I : Cardinal.mk I = Order.succ μ := by
  rw [I,Cardinal.mk_toType,Cardinal.card_ord]

@[simp] theorem cardinal_κ : Cardinal.mk κ = Cardinal.aleph 1 := by
  rw [κ,Cardinal.mk_toType,Cardinal.card_ord]

instance : Infinite I := Cardinal.aleph0_le_mk_iff.mp
  (by rw [cardinal_I]; exact aleph0_le_μ.trans (Order.le_succ μ))
instance : Uncountable κ := Cardinal.aleph0_lt_mk_iff.mp
  (by rw [cardinal_κ]; exact Cardinal.aleph0_lt_aleph_one)

theorem size_lt : Cardinal.mk T < Cardinal.mk I := by
  rw [cardinal_T,cardinal_I]; exact Order.lt_succ μ

abbrev P := ProductForcing.Poset T I κ

def S : SymmetricSystem.{0} P (Equiv.Perm I) := ProductForcing.system aleph0_le_μ

theorem forces_ZF (p : P) : ∀ φ ∈ SetLanguage.ZF, S.Forces Fin.elim0 p φ := S.forces_ZF p

theorem forces_not_AC (p : P) : S.Forces Fin.elim0 p SetLanguage.AC.neg :=
  ProductForcing.forces_not_AC aleph0_le_μ cardinal_T size_lt finiteMergers T.e
    complement_cardinal (posetCode κ) (posetCode_injective κ) p

/-- Consistency of the ZF + ¬AC subtheory. The full target, also including
PP and ordinal-indexed choice, is proved below in `consistent_target`. -/
theorem consistent_ZF_not_AC : Consistent (Set.insert SetLanguage.AC.neg SetLanguage.ZF) := by
  apply S.consistent_of_forces (⊤ : P)
  intro φ hφ
  rcases hφ with rfl | hφ
  · exact forces_not_AC ⊤
  · exact forces_ZF ⊤ φ hφ

end
end PartitionConsistency.ConcreteSystem


/-! ## LabelFiber -/

namespace PartitionConsistency.LocalDiagramSystem
universe u
open DiagramOrder DiagramForcing
variable {M I : Type u} [LeftCancelMonoid M] [IsConical M]
noncomputable section

/-- Label availability is literal membership in the subdiagram range. -/
theorem label_available_iff (r : Diagram M I) (j : r.range) (n : M) :
    (labelSystem (M := M) (I := I)).Available r j n ↔ j.val ∈ (r.sub n).range := by
  constructor
  · rintro ⟨k,hk⟩
    exact (congrArg Subtype.val hk) ▸ k.property
  · intro hj
    exact ⟨⟨j.val,hj⟩,rfl⟩

/-- The availability test at a center is precisely left divisibility. -/
theorem label_available_center (r : Diagram M I) (k n : M) :
    (labelSystem (M := M) (I := I)).Available r ⟨r k,⟨k,rfl⟩⟩ n ↔ n ∣ k := by
  rw [label_available_iff]
  constructor
  · rintro ⟨x,hx⟩
    exact ⟨x,(r.injective hx).symm⟩
  · rintro ⟨x,hx⟩
    exact ⟨x,congrArg r hx.symm⟩

/-- A probe profile supplies a genuine exact-fiber label, rather than merely
an element of the ambient label range. -/
def labelFiberEmbedding {q : Diagram M I} (w : Vertex q) {K : Type u}
    (m : K → M) (hinj : Function.Injective m)
    (hprofile : ∀ i (x : M), x ∣ w.index ∧ x ∣ m i ↔ x ∈ w.ideal.carrier) :
    K ↪ (labelSystem (M := M) (I := I)).vertexFiber w where
  toFun i := ⟨⟨w.diagram (m i),⟨m i,rfl⟩⟩,by
    apply ConeIdeal.ext
    ext n
    change n ≤ w.index ∧ (labelSystem (M := M) (I := I)).Available
      w.diagram ⟨w.diagram (m i),⟨m i,rfl⟩⟩ n ↔ _
    erw [label_available_center,LeftDivOrder.le_iff_dvd]
    exact hprofile i n⟩
  inj' := by
    intro i j h
    apply hinj
    apply w.diagram.injective
    exact congrArg (fun z : (labelSystem (M := M) (I := I)).vertexFiber w => z.val.val) h

/-- The common ground subset of label indices underlying a component. -/
def labelFiberSet {q : Diagram M I} (w : Vertex q) : Set I :=
  Set.range (fun x : (labelSystem (M := M) (I := I)).vertexFiber w => x.val.val)

theorem labelFiberSet_subset {q : Diagram M I} (w : Vertex q) :
    labelFiberSet w ⊆ w.diagram.range := by
  rintro _ ⟨x,rfl⟩
  exact x.val.property

/-- Contractions act as the identity on label indices. -/
theorem label_arrowMap_val (hj : HasConditionalJoins (LeftDivOrder M))
    {q : Diagram M I} {w z : Vertex q} (f : w.Arrow z)
    (x : (labelSystem (M := M) (I := I)).vertexFiber z) :
    ((labelSystem (M := M) (I := I)).arrowMap hj f x).val.val = x.val.val := rfl

theorem labelFiberSet_arrow (hj : HasConditionalJoins (LeftDivOrder M))
    {q : Diagram M I} {w z : Vertex q} (f : w.Arrow z) :
    labelFiberSet w = labelFiberSet z := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x,rfl⟩
    obtain ⟨y,hy⟩ := ((labelSystem (M := M) (I := I)).arrowMap_bijective hj f).2 x
    exact ⟨y,congrArg (fun t => t.val.val) hy⟩
  · rintro _ ⟨x,rfl⟩
    exact ⟨(labelSystem (M := M) (I := I)).arrowMap hj f x,rfl⟩

/-- The label fibers of a whole connected component are literally the same
subset of the coordinate set, not just equinumerous sets. -/
theorem labelFiberSet_common (hj : HasConditionalJoins (LeftDivOrder M))
    {q : Diagram M I} {w z : Vertex q} (h : Vertex.Common w z) :
    labelFiberSet w = labelFiberSet z := by
  obtain ⟨t,⟨f⟩,⟨g⟩⟩ := h
  exact (labelFiberSet_arrow hj f).trans (labelFiberSet_arrow hj g).symm

end
end PartitionConsistency.LocalDiagramSystem

namespace PartitionConsistency.MonoidConstruction.Saturation
universe u
open DiagramOrder DiagramForcing LocalDiagramSystem
noncomputable section
variable (M : Object.{u}) (K : Type u) [Nonempty K]

/-- The source's exact label-fiber count in the actual executed saturated
monoid. All ideals at all final vertices are covered. No count of symbolic
E-classes is postulated here. -/
theorem labelFiber_cardinal {μ : Cardinal.{u}} (hω : Cardinal.aleph 1 ≤ μ)
    (hpow : μ ^ Cardinal.aleph0 = μ) (hM : Cardinal.mk M ≤ μ) (hK : Cardinal.mk K = μ)
    {I : Type u} {q : Diagram (target M K) I} (w : Vertex q) :
    Cardinal.mk ((labelSystem (M := target M K) (I := I)).vertexFiber w) = μ := by
  apply le_antisymm
  · have hh := Cardinal.mk_subtype_le (fun x : w.diagram.range =>
        (labelSystem (M := target M K) (I := I)).availability w.diagram w.index x = w.ideal)
    exact hh.trans_eq ((Diagram.cardinal_range w.diagram).trans (target_cardinal M K hω hpow hM hK))
  · obtain ⟨m,hinj,hm,_⟩ := ideal_probes M K w.index (target M K).e (target M K).e_ne_one w.ideal
    rw [← hK]
    exact Cardinal.mk_le_of_injective (labelFiberEmbedding w m hinj (fun i => (hm i).2.2.1)).injective

/-- Gluing changes neither this label fiber nor its cardinality. -/
theorem gluedLabel_cardinal {μ : Cardinal.{u}} (hω : Cardinal.aleph 1 ≤ μ)
    (hpow : μ ^ Cardinal.aleph0 = μ) (hM : Cardinal.mk M ≤ μ) (hK : Cardinal.mk K = μ)
    {I : Type u} {q : Diagram (target M K) I} (w : Vertex q) :
    Cardinal.mk ((labelSystem (M := target M K) (I := I)).Glued (target M K).joins w) = μ := by
  rw [← Cardinal.mk_congr ((labelSystem (M := target M K) (I := I)).fiberEquivGlued
    (target M K).joins w w (Vertex.Common.refl w))]
  exact labelFiber_cardinal M K hω hpow hM hK w

end
end PartitionConsistency.MonoidConstruction.Saturation


/-! ## Stabilizer -/

namespace PartitionConsistency.LocalDiagramSystem.Vertex
universe u
open DiagramOrder DiagramForcing
variable {M I : Type u} [LeftCancelMonoid M] [IsConical M]
variable {q : Diagram M I}
noncomputable section

abbrev RootGroup (q : Diagram M I) := SupportFilter.Fix q.range

/-- The action fixes the chosen root diagram literally, and leaves the
monoid index and ideal unchanged. -/
def permute (π : RootGroup q) (v : Vertex q) : Vertex q where
  diagram := v.diagram.permute π.val
  index := v.index
  root := by
    rw [← Diagram.permute_sub,v.root]
    exact Diagram.permute_eq_of_fixes_range _ q ((SupportFilter.mem_Fix _ _).mp π.property)
  ideal := v.ideal

@[simp] theorem permute_one (v : Vertex q) : permute 1 v = v := by
  cases v
  simp only [permute,Subgroup.coe_one,Diagram.permute_one]

@[simp] theorem permute_mul (π σ : RootGroup q) (v : Vertex q) :
    permute (π * σ) v = permute π (permute σ v) := by
  cases v
  simp only [permute,Subgroup.coe_mul,Diagram.permute_mul]

instance : MulAction (RootGroup q) (Vertex q) where
  smul := permute
  one_smul := permute_one
  mul_smul := permute_mul

@[simp] theorem smul_diagram (π : RootGroup q) (v : Vertex q) :
    (π • v).diagram = v.diagram.permute π.val := rfl
@[simp] theorem smul_index (π : RootGroup q) (v : Vertex q) : (π • v).index = v.index := rfl
@[simp] theorem smul_ideal (π : RootGroup q) (v : Vertex q) : (π • v).ideal = v.ideal := rfl

/-- Coordinate transport preserves the entire contraction, not merely a
relation between ranges. -/
def Arrow.move {v w : Vertex q} (π : RootGroup q) (f : Arrow v w) :
    Arrow (π • v) (π • w) where
  index := f.index
  mem := f.mem
  diagram := by rw [smul_diagram,smul_diagram,← Diagram.permute_sub,f.diagram]
  ideal := f.ideal

theorem Common.move {v w : Vertex q} (π : RootGroup q) (h : Common v w) :
    Common (π • v) (π • w) := by
  obtain ⟨t,⟨f⟩,⟨g⟩⟩ := h
  exact ⟨π • t,⟨f.move π⟩,⟨g.move π⟩⟩

/-- Setwise stabilizer of the component of v. `Common` is already proved
to be exactly connectedness under finite contraction zigzags. -/
def componentStabilizer (hj : HasConditionalJoins (LeftDivOrder M)) (v : Vertex q) :
    Subgroup (RootGroup q) where
  carrier := {π | Common v (π • v)}
  one_mem' := by
    change Common v (1 • v)
    simpa only [one_smul] using Common.refl v
  mul_mem' := by
    intro π σ hπ hσ
    change Common v ((π * σ) • v)
    simpa only [mul_smul] using hπ.trans hj (hσ.move π)
  inv_mem' := by
    intro π hπ
    change Common v (π⁻¹ • v)
    simpa only [inv_smul_smul] using (hπ.move π⁻¹).symm

theorem common_moved (hj : HasConditionalJoins (LeftDivOrder M)) (v : Vertex q)
    (π : componentStabilizer hj v) {w : Vertex q} (hw : Common v w) :
    Common v (π.val • w) := π.property.trans hj (hw.move π.val)

/-- A concrete cofinal chain in a component. Its arrows contain actual
translation indices, and the initial term is the chosen vertex. -/
structure Chain (v : Vertex q) where
  vertex : ℕ → Vertex q
  first : vertex 0 = v
  increasing : ∀ i j, i ≤ j → Nonempty (Arrow (vertex i) (vertex j))
  cofinal : ∀ w, Common v w → ∃ i, Nonempty (Arrow w (vertex i))

/-- Chains are constructed from the height-cost theorem, not postulated
when they are used with the saturated monoid. -/
theorem exists_chain (hj : HasConditionalJoins (LeftDivOrder M))
    (H : HeightCost (LeftDivOrder M)) (v : Vertex q) : Nonempty (Chain v) := by
  obtain ⟨f,hf,hm,_,hc⟩ := component_cofinal_chain hj H v
  exact ⟨⟨f,hf,hm,hc⟩⟩

namespace Chain
variable {v : Vertex q} (C : Chain v)

theorem common (i : ℕ) : Common v (C.vertex i) := by
  have h := Common.of_arrow (C.increasing 0 i (Nat.zero_le i)).some
  rwa [C.first] at h

theorem ranges_antitone : Antitone (fun i => (C.vertex i).diagram.range) := by
  intro i j hij
  obtain ⟨f⟩ := C.increasing i j hij
  exact Diagram.range_antitone (show (C.vertex i).diagram ≤ (C.vertex j).diagram from
    ⟨f.index,f.diagram⟩)

/-- The increasing union of pointwise tail fixers, regarded inside the actual
component stabilizer. -/
def tailFixer (hj : HasConditionalJoins (LeftDivOrder M)) :
    Subgroup (componentStabilizer hj v) where
  carrier := {π | ∃ i, ∀ j ∈ (C.vertex i).diagram.range, π.val.val j = j}
  one_mem' := ⟨0,fun _ _ => rfl⟩
  mul_mem' := by
    rintro π σ ⟨i,hi⟩ ⟨k,hk⟩
    refine ⟨max i k,?_⟩
    intro j hj
    change π.val.val (σ.val.val j) = j
    rw [hk j (C.ranges_antitone (le_max_right _ _) hj),hi j (C.ranges_antitone (le_max_left _ _) hj)]
  inv_mem' := by
    rintro π ⟨i,hi⟩
    refine ⟨i,?_⟩
    intro j hj
    change π.val.val.symm j = j
    exact π.val.val.symm_apply_eq.mpr (hi j hj).symm

/-- Membership is eventual pointwise fixation, not a condition on an assigned
bijection or on the result of the quotient construction. -/
theorem mem_tailFixer (hj : HasConditionalJoins (LeftDivOrder M))
    (π : componentStabilizer hj v) : π ∈ C.tailFixer hj ↔
      ∃ i, ∀ j ∈ (C.vertex i).diagram.range, π.val.val j = j := Iff.rfl

/-- A permutation fixing a chain diagram belongs to the component stabilizer.
This justifies viewing the displayed union of full fixers inside that group. -/
theorem fixes_mem_stabilizer (hj : HasConditionalJoins (LeftDivOrder M))
    (π : RootGroup q) (i : ℕ)
    (h : ∀ j ∈ (C.vertex i).diagram.range, π.val j = j) :
    π ∈ componentStabilizer hj v := by
  have hf : π • C.vertex i = C.vertex i := by
    have he := Diagram.permute_eq_of_fixes_range π.val (C.vertex i).diagram h
    have hperm : ∀ (w : Vertex q), w.diagram.permute π.val = w.diagram → π • w = w := by
      rintro ⟨r,a,hr,U⟩ he
      change ({diagram := r.permute π.val,index := a,root := _,ideal := U} : Vertex q) = _
      simp only [he]
    exact hperm _ he
  exact (C.common i).trans hj (by simpa only [hf] using ((C.common i).move π).symm)

/-- Cofinality of the chain makes the union of its tail fixers normal. The
conjugating permutation is allowed to move the entire chain. -/
instance tailFixer_normal (hj : HasConditionalJoins (LeftDivOrder M)) :
    (C.tailFixer hj).Normal where
  conj_mem := by
    rintro k ⟨i,hi⟩ σ
    obtain ⟨j,⟨f⟩⟩ := C.cofinal (σ.val • C.vertex i) (common_moved hj v σ (C.common i))
    refine ⟨j,?_⟩
    intro x hx
    have himage : x ∈ ((C.vertex i).diagram.permute σ.val.val).range :=
      Diagram.range_antitone (show (σ.val • C.vertex i).diagram ≤ (C.vertex j).diagram from
        ⟨f.index,f.diagram⟩) hx
    rw [Diagram.range_permute] at himage
    obtain ⟨y,hy,rfl⟩ := himage
    change σ.val.val (k.val.val (σ.val.val.symm (σ.val.val y))) = σ.val.val y
    rw [Equiv.symm_apply_apply,hi y hy]

/-- The name-independent label set is fixed pointwise by every tail fixer. -/
theorem tailFixer_fixes_labels (hj : HasConditionalJoins (LeftDivOrder M))
    (k : C.tailFixer hj) (j : I) (hjv : j ∈ labelFiberSet v) : k.val.val.val j = j := by
  obtain ⟨i,hi⟩ := k.property
  apply hi
  apply labelFiberSet_subset (C.vertex i)
  rwa [← labelFiberSet_common hj (C.common i)]

end Chain
end
end PartitionConsistency.LocalDiagramSystem.Vertex

end OAI
