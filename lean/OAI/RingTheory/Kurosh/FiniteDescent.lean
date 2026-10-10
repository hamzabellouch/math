import Mathlib

namespace OAI

/-! Finite descent over algebraic central extensions and the actual center. -/

namespace KuroshConstruction

open Module

variable {K F D : Type*} [Field K] [Field F] [Ring D]
  [Algebra K F] [Algebra F D] [Algebra K D] [IsScalarTower K F D]

omit [Algebra K D] [IsScalarTower K F D] in
theorem mem_span_of_coordinates {ι : Type*} [Fintype ι]
    (b : Basis ι F D) (E : IntermediateField K F) (x : D)
    (hx : ∀ i, b.repr x i ∈ E) :
    x ∈ Submodule.span E (Set.range b) := by
  classical
  rw [← b.sum_repr x]
  apply Submodule.sum_mem
  intro i _
  have hm : b i ∈ Submodule.span E (Set.range b) :=
    Submodule.subset_span ⟨i, rfl⟩
  exact (Submodule.span E (Set.range b)).smul_mem ⟨b.repr x i, hx i⟩ hm

omit [Algebra K D] [IsScalarTower K F D] in
theorem span_mul_mem_of_structure_constants {ι : Type*} [Fintype ι]
    (b : Basis ι F D) (E : IntermediateField K F)
    (hmul : ∀ i j h, b.repr (b i * b j) h ∈ E)
    {x y : D} (hx : x ∈ Submodule.span E (Set.range b))
    (hy : y ∈ Submodule.span E (Set.range b)) :
    x * y ∈ Submodule.span E (Set.range b) := by
  refine Submodule.span_induction₂ (p := fun x y _ _ =>
    x * y ∈ Submodule.span E (Set.range b)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    exact mem_span_of_coordinates b E _ (hmul i j)
  · intro y _
    simp
  · intro x _
    simp
  · intro x y z _ _ _ hxz hyz
    simpa only [add_mul] using (Submodule.span E (Set.range b)).add_mem hxz hyz
  · intro x y z _ _ _ hxy hxz
    simpa only [mul_add] using (Submodule.span E (Set.range b)).add_mem hxy hxz
  · intro r x y _ _ hxy
    simpa only [smul_mul_assoc] using (Submodule.span E (Set.range b)).smul_mem r hxy
  · intro r x y _ _ hxy
    simpa only [mul_smul_comm] using (Submodule.span E (Set.range b)).smul_mem r hxy

theorem finite_descent_of_basis {ι : Type*} [Fintype ι]
    [Algebra.IsAlgebraic K F] (b : Basis ι F D)
    (s : Finset D) (hs : Algebra.adjoin K (s : Set D) = ⊤) :
    Module.Finite K D := by
  classical
  let T : Finset D := {1} ∪ s ∪
    (Finset.univ.product Finset.univ).image (fun ij : ι × ι => b ij.1 * b ij.2)
  let C : Finset F := T.biUnion fun x => Finset.univ.image (b.repr x)
  let E : IntermediateField K F := IntermediateField.adjoin K (C : Set F)
  have hcoord (x : D) (hx : x ∈ T) (i : ι) : b.repr x i ∈ E := by
    apply IntermediateField.subset_adjoin K (C : Set F)
    exact Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
  have hone : (1 : D) ∈ Submodule.span E (Set.range b) := by
    apply mem_span_of_coordinates b E
    exact hcoord 1 (by simp [T])
  have hgen (x : D) (hx : x ∈ s) : x ∈ Submodule.span E (Set.range b) := by
    apply mem_span_of_coordinates b E
    exact hcoord x (by simp [T, hx])
  have hmul (i j h : ι) : b.repr (b i * b j) h ∈ E := by
    apply hcoord
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨(i,j), by simp, rfl⟩
  have htop : Submodule.span E (Set.range b) = ⊤ := by
    apply top_unique
    intro x hxTop
    clear hxTop
    have hx : x ∈ Algebra.adjoin K (s : Set D) := by rw [hs]; trivial
    induction hx using Algebra.adjoin_induction with
    | mem x hx => exact hgen x hx
    | algebraMap r =>
        rw [Algebra.algebraMap_eq_smul_one]
        exact (Submodule.span E (Set.range b)).restrictScalars K |>.smul_mem r hone
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | mul x y _ _ hx hy => exact span_mul_mem_of_structure_constants b E hmul hx hy
  let : Module.Finite K E := IntermediateField.finiteDimensional_adjoin
    (fun x _ => (Algebra.IsAlgebraic.isAlgebraic (R := K) x).isIntegral)
  let : Module.Finite E D := ⟨by
    rw [← htop]
    exact Submodule.fg_span (Set.finite_range b)⟩
  exact Module.Finite.trans E D

theorem finite_descent [Module.Finite F D] [Algebra.IsAlgebraic K F]
    (s : Finset D) (hs : Algebra.adjoin K (s : Set D) = ⊤) :
    Module.Finite K D :=
  finite_descent_of_basis (Module.finBasis F D) s hs

section ActualCenter

variable {k A : Type*} [Field k] [DivisionRing A] [Algebra k A]

abbrev algebraInCenter : Algebra k (Subring.center A) :=
  inferInstanceAs (Algebra k (Subalgebra.center k A))

theorem not_finite_over_center [Algebra.IsAlgebraic k A]
    (s : Finset A) (hs : Algebra.adjoin k (s : Set A) = ⊤)
    (hinf : ¬ Module.Finite k A) :
    ¬ Module.Finite (Subring.center A) A := by
  intro hfin
  let : Algebra k (Subring.center A) := algebraInCenter
  let : IsScalarTower k (Subring.center A) A :=
    inferInstanceAs (IsScalarTower k (Subalgebra.center k A) A)
  let : Algebra.IsAlgebraic k (Subring.center A) :=
    Algebra.IsAlgebraic.of_injective (Subalgebra.center k A).val Subtype.val_injective
  exact hinf (finite_descent (F := Subring.center A) s hs)

theorem adjoin_center_eq_top {s : Set A} (hs : Algebra.adjoin k s = ⊤) :
    Algebra.adjoin (Subring.center A) s = ⊤ := by
  let : Algebra k (Subring.center A) := algebraInCenter
  let : IsScalarTower k (Subring.center A) A :=
    inferInstanceAs (IsScalarTower k (Subalgebra.center k A) A)
  have hle : Algebra.adjoin k s ≤
      (Algebra.adjoin (Subring.center A) s).restrictScalars k :=
    Algebra.adjoin_le_iff.mpr (Algebra.subset_adjoin)
  rw [hs] at hle
  apply top_unique
  intro x _
  exact hle (by trivial)

theorem algebraic_over_center [Algebra.IsAlgebraic k A] (x : A) :
    IsAlgebraic (Subring.center A) x := by
  let : Algebra k (Subring.center A) := algebraInCenter
  let : IsScalarTower k (Subring.center A) A :=
    inferInstanceAs (IsScalarTower k (Subalgebra.center k A) A)
  exact (Algebra.IsAlgebraic.isAlgebraic (R := k) x).tower_top (Subring.center A)

end ActualCenter

def centerDivisionAdjoin (D : Type) [DivisionRing D] (s : Set D) : Subring D :=
  sInf {S : Subring D | Subring.center D ≤ S ∧ s ⊆ S ∧
    ∀ a : D, a ∈ S → a⁻¹ ∈ S}

theorem center_le_centerDivisionAdjoin {D : Type} [DivisionRing D] (s : Set D) :
    Subring.center D ≤ centerDivisionAdjoin D s := by
  exact le_sInf fun _ hS => hS.1

theorem subset_centerDivisionAdjoin {D : Type} [DivisionRing D] (s : Set D) :
    s ⊆ centerDivisionAdjoin D s := by
  intro a ha
  exact Subring.mem_sInf.mpr fun _ hS => hS.2.1 ha

theorem centerDivisionAdjoin_inv_mem {D : Type} [DivisionRing D] {s : Set D}
    {a : D} (ha : a ∈ centerDivisionAdjoin D s) :
    a⁻¹ ∈ centerDivisionAdjoin D s := by
  apply Subring.mem_sInf.mpr
  intro S hS
  exact hS.2.2 a (Subring.mem_sInf.mp ha S hS)

theorem centerDivisionAdjoin_le {D : Type} [DivisionRing D] {s : Set D}
    {S : Subring D} (hc : Subring.center D ≤ S) (hs : s ⊆ S)
    (hinv : ∀ a : D, a ∈ S → a⁻¹ ∈ S) :
    centerDivisionAdjoin D s ≤ S := by
  exact sInf_le ⟨hc, hs, hinv⟩

theorem centerDivisionAdjoin_eq_top {A : Type} [DivisionRing A] {s : Set A}
    (hs : Algebra.adjoin (Subring.center A) s = ⊤) :
    centerDivisionAdjoin A s = ⊤ := by
  apply top_unique
  intro x _
  apply Subring.mem_sInf.mpr
  rintro S ⟨hc, hgen, _⟩
  let B : Subalgebra (Subring.center A) A :=
    { S with
      algebraMap_mem' := fun z => hc z.property }
  have hle : Algebra.adjoin (Subring.center A) s ≤ B :=
    Algebra.adjoin_le_iff.mpr hgen
  rw [hs] at hle
  exact hle (by trivial)

end KuroshConstruction

end OAI
