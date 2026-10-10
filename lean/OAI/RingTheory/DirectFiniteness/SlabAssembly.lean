import OAI.RingTheory.DirectFiniteness.PlaneOperators

namespace OAI

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q A R E : Type} [Field Q] [CharP Q 2] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E] [Fintype A] [Fintype Q] [Fintype E]
namespace DirectionFrame
variable (F : DirectionFrame Q A R E) (O : Finset A)
  (P : SlabVariable F → Plane Q E) (hP : F.SuccessfulSlabs O P)

include hP in
lemma SlabKey.exists_patch (j : R × Q) (k : F.SlabKey P j) :
    Nonempty (F.SlabPatch j (P ⟨j,k.1⟩) O (k.points F P j)) := by
  by_cases hh : ∃ o ∈ O, o ∈ k.points F P j
  · obtain ⟨o,ho,hob⟩ := hh
    have he : k.points F P j = cosetPoints (F.slabMap j (P ⟨j,k.1⟩)).range o :=
      (congrArg Subtype.val (AffineCoset.eq_of_mem _ hob)).symm
    rw [he]
    obtain ⟨J,hJ⟩ := exists_plane_operator Q E (P ⟨j,k.1⟩)
    apply F.axisSlabPatch j (P ⟨j,k.1⟩) o O ho _ J hJ
    intro x hx hxb
    exact (k.holes_unique F P j O hP ho hx hob (he ▸ hxb)).symm
  · obtain ⟨o,ho⟩ := k.nonempty F P j
    have he : k.points F P j = cosetPoints (F.slabMap j (P ⟨j,k.1⟩)).range o :=
      (congrArg Subtype.val (AffineCoset.eq_of_mem _ ho)).symm
    rw [he]
    apply F.emptySlabPatch j (P ⟨j,k.1⟩) o O
    rw [Finset.disjoint_left]
    intro x hx hxb
    exact hh ⟨x,hx,he ▸ hxb⟩

structure Preliminary where
  part : R × Q → LinePartition (Q := Q) (A := A)
  axis : ∀ j o, o ∈ O → (part j).through o = cosetPoints (F.D j) o
  generic : ∀ j x, Disjoint ((part j).through x) O →
    ∀ y ∈ (part j).through x, ∀ z ∈ (part j).through x, z ≠ y →
    ∃ c : Q, ∃ e : E, e ≠ 0 ∧ e ∈ (P ⟨j,AffineCoset.of (F.U j) y⟩).val ∧ F.u j (c,e)=z-y

include hP in
lemma exists_preliminary : Nonempty (F.Preliminary O P) := by
  let T : ∀ j (k : F.SlabKey P j), F.SlabPatch j (P ⟨j,k.1⟩) O (k.points F P j) :=
    fun j k => (k.exists_patch F O P hP j).some
  let L (j : R × Q) : LinePartition (Q := Q) (A := A) :=
    gluePartition (fun k : F.SlabKey P j => k.points F P j) (F.slabKeyOf P j)
      (F.mem_slabKeyOf P j) (F.slabKeyOf_stable P j) (fun k => (T j k).partition)
  refine ⟨⟨L,?_,?_⟩⟩
  · intro j o ho
    exact (T j (F.slabKeyOf P j o)).axis ⟨o,F.mem_slabKeyOf P j o⟩ ho
  · intro j x hx y hy z hz hne
    let k := F.slabKeyOf P j x
    have hh := (T j k).generic ⟨x,F.mem_slabKeyOf P j x⟩ hx y hy z hz hne
    have hyC : y ∈ k.1.val := k.2.property ((T j k).partition.subset _ hy)
    have he : AffineCoset.of (F.U j) y = k.1 := AffineCoset.eq_of_mem _ hyC
    simpa only [he] using hh

end DirectionFrame
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
