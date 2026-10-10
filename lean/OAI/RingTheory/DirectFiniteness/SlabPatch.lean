import OAI.RingTheory.DirectFiniteness.ModelPartition

namespace OAI

universe u_1 u_2 u_3 u_4

noncomputable section
open scoped Classical
open Module
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q : Type u_1} {A : Type u_2} {R : Type u_3} {E : Type u_4} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E] [Fintype A] [Fintype Q] [Fintype E]
namespace DirectionFrame
variable (F : DirectionFrame Q A R E) (j : R × Q) (P : Plane Q E)

def slabImage (o : A) (l : Finset (P.val × Q)) : Finset A :=
  l.image (fun x => o+F.slabMap j P x)

omit [Fintype E] in
lemma slabImage_axis (o : A) : F.slabImage j P o modelAxis = cosetPoints (F.D j) o := by
  ext point
  rw [slabImage,Finset.mem_image,mem_cosetPoints]
  constructor
  · rintro ⟨⟨vector,scalar⟩,membership,rfl⟩
    have vector_zero : vector = 0 := (mem_modelAxis _).mp membership
    subst vector
    exact ⟨scalar,by rw [F.slabMap_axis,add_sub_cancel_left]⟩
  · rintro ⟨scalar,scalar_spec⟩
    refine ⟨(0,scalar),(mem_modelAxis _).mpr rfl,?_⟩
    rw [F.slabMap_axis,scalar_spec,add_comm,sub_add_cancel]

omit [Fintype A] [Fintype Q] [Fintype E] in
lemma slabImage_pair (o : A) (l : Finset (P.val × Q))
    (hproj : ∀ x ∈ l, ∀ y ∈ l, y ≠ x → y.1-x.1 ≠ 0)
    {x y : A} (hx : x ∈ F.slabImage j P o l) (hy : y ∈ F.slabImage j P o l) (hne : y ≠ x) :
    ∃ c : Q, ∃ e : E, e ≠ 0 ∧ e ∈ P.val ∧ F.u j (c,e)=y-x := by
  obtain ⟨x',hx',rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨y',hy',rfl⟩ := Finset.mem_image.mp hy
  have hne' : y' ≠ x' := fun h => hne (h ▸ rfl)
  refine ⟨y'.2-x'.2,y'.1.val-x'.1.val,?_,P.val.sub_mem y'.1.property x'.1.property,?_⟩
  · intro h
    exact hproj x' hx' y' hy' hne' (Subtype.ext h)
  · change F.slabMap j P (y'-x') = _
    rw [map_sub]
    abel

structure SlabPatch (O S : Finset A) where
  partition : PartitionOn (Q := Q) S
  axis : ∀ o : S, o.val ∈ O → partition.through o = cosetPoints (F.D j) o.val
  generic : ∀ x : S, Disjoint (partition.through x) O →
    ∀ y ∈ partition.through x, ∀ z ∈ partition.through x, z ≠ y →
    ∃ c : Q, ∃ e : E, e ≠ 0 ∧ e ∈ P.val ∧ F.u j (c,e)=z-y

lemma axisSlabPatch (o : A) (O : Finset A) (ho : o ∈ O)
    (hu : ∀ x ∈ O, x ∈ cosetPoints (F.slabMap j P).range o → x=o)
    (J : P.val →ₗ[Q] P.val) (hJ : NoEigenvector J) :
    Nonempty (F.SlabPatch j P O (cosetPoints (F.slabMap j P).range o)) := by
  let m := F.slabMap j P
  let hm := F.slabMap_injective j P
  let L := axisPartition P.property J hJ
  let e := PartitionOn.parametrization m hm o
  let T := PartitionOn.image m hm o L
  refine ⟨⟨T,?_,?_⟩⟩
  · intro x hx
    have hxv : x.val=o := hu x.val hx x.property
    have hxe : x=e 0 := Subtype.ext (by simpa [e,PartitionOn.parametrization_val] using hxv)
    rw [hxe]
    change (PartitionOn.image m hm o L).through (PartitionOn.parametrization m hm o 0) = _
    rw [PartitionOn.image_through]
    change F.slabImage j P o ((axisPartition P.property J hJ).through 0) = _
    rw [axisPartition_through_zero,F.slabImage_axis]
    simp [e,PartitionOn.parametrization_val]
  · intro x hx y hy z hz hne
    let x' := e.symm x
    have hxp : x'.1 ≠ 0 := by
      intro he
      have hmem : (0 : P.val × Q) ∈ L.through x' :=
        (axisPartition_zero_mem_iff P.property J hJ x').mpr he
      have hoT : o ∈ T.through x := by
        refine Finset.mem_image.mpr ⟨0,hmem,?_⟩
        simp
      exact Finset.disjoint_left.mp hx hoT ho
    apply F.slabImage_pair j P o (L.through x') _ hy hz hne
    intro a ha b hb hba
    exact axisPartition_projection P.property J hJ hxp ha hb hba

lemma emptySlabPatch (o : A) (O : Finset A)
    (hu : Disjoint O (cosetPoints (F.slabMap j P).range o)) :
    Nonempty (F.SlabPatch j P O (cosetPoints (F.slabMap j P).range o)) := by
  have hn : Nontrivial P.val := Module.nontrivial_of_finrank_pos (by rw [P.property]; decide : 0 < finrank Q P.val)
  obtain ⟨v,hv⟩ := exists_ne (0 : P.val)
  let m := F.slabMap j P
  let hm := F.slabMap_injective j P
  let L := parallelPlanePartition (Q := Q) v hv
  let e := PartitionOn.parametrization m hm o
  let T := PartitionOn.image m hm o L
  refine ⟨⟨T,?_,?_⟩⟩
  · intro x hx
    exact False.elim (Finset.disjoint_left.mp hu hx x.property)
  · intro x _ y hy z hz hne
    apply F.slabImage_pair j P o (L.through (e.symm x)) _ hy hz hne
    intro a ha b hb hba
    exact parallelPlanePartition_projection (Q := Q) v hv ha hb hba

end DirectionFrame
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
