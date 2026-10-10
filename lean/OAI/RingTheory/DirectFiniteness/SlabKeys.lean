import OAI.RingTheory.DirectFiniteness.PartialPartition

namespace OAI

universe u_1 u_2 u_3 u_4

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q : Type u_1} {A : Type u_2} {R : Type u_3} {E : Type u_4} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E] [Fintype A]
namespace DirectionFrame
variable (F : DirectionFrame Q A R E)

local instance identityRingHomSurjective : RingHomSurjective (RingHom.id Q) := inferInstance

def slabMap (j : R × Q) (P : Plane Q E) : (P.val × Q) →ₗ[Q] A where
  toFun x := F.u j (x.2,x.1.val)
  map_add' x y := by simpa using (F.u j).map_add (x.2,x.1.val) (y.2,y.1.val)
  map_smul' c x := by simpa using (F.u j).map_smul c (x.2,x.1.val)

omit [Fintype A] in
lemma slabMap_injective (j : R × Q) (P : Plane Q E) : Function.Injective (F.slabMap j P) := by
  intro x y h
  have h' := F.u_injective j h
  exact Prod.ext (Subtype.ext (congrArg Prod.snd h')) (congrArg Prod.fst h')

omit [Fintype A] in
lemma slabMap_range_le (j : R × Q) (P : Plane Q E) : (F.slabMap j P).range ≤ F.U j := by
  rintro x ⟨z,rfl⟩
  exact ⟨(z.2,z.1.val),rfl⟩

omit [Fintype A] in
@[simp] lemma slabMap_axis (j : R × Q) (P : Plane Q E) (t : Q) :
    F.slabMap j P (0,t) = F.d j t := by simp [slabMap]

variable (P : SlabVariable F → Plane Q E) (j : R × Q)

def SlabKey := Σ C : AffineCoset (F.U j),
  {B : AffineCoset (F.slabMap j (P ⟨j,C⟩)).range // B.val ⊆ C.val}

def SlabKey.points (k : F.SlabKey P j) : Finset A := k.2.val.val

lemma SlabKey.nonempty (k : F.SlabKey P j) : (k.points F P j).Nonempty := k.2.val.nonempty _

def slabKeyOf (x : A) : F.SlabKey P j :=
  ⟨AffineCoset.of (F.U j) x,AffineCoset.of (F.slabMap j (P ⟨j,AffineCoset.of (F.U j) x⟩)).range x,by
    intro y hy
    exact (mem_cosetPoints _ _ _).mpr (F.slabMap_range_le j _ ((mem_cosetPoints _ _ _).mp hy))⟩

lemma mem_slabKeyOf (x : A) : x ∈ (F.slabKeyOf P j x).points F P j := self_mem_cosetPoints _ _

lemma SlabKey.unique {k k' : F.SlabKey P j} {x : A}
    (hx : x ∈ k.points F P j) (hx' : x ∈ k'.points F P j) : k=k' := by
  obtain ⟨C,⟨B,hB⟩⟩ := k
  obtain ⟨C',⟨B',hB'⟩⟩ := k'
  have hc : C=C' := (AffineCoset.eq_of_mem _ (hB hx)).symm.trans (AffineCoset.eq_of_mem _ (hB' hx'))
  subst C'
  have hb : B=B' := (AffineCoset.eq_of_mem _ hx).symm.trans (AffineCoset.eq_of_mem _ hx')
  subst B'
  rfl

lemma slabKeyOf_eq_of_mem {k : F.SlabKey P j} {x : A} (hx : x ∈ k.points F P j) :
    F.slabKeyOf P j x=k := SlabKey.unique F P j (F.mem_slabKeyOf P j x) hx

lemma slabKeyOf_stable (x y : A) (hy : y ∈ (F.slabKeyOf P j x).points F P j) :
    F.slabKeyOf P j y=F.slabKeyOf P j x := F.slabKeyOf_eq_of_mem P j hy

lemma SlabKey.diff {k : F.SlabKey P j} {x y : A} (hx : x ∈ k.points F P j)
    (hy : y ∈ k.points F P j) : y-x ∈ (F.slabMap j (P ⟨j,k.1⟩)).range := by
  exact (AffineCoset.of_eq_iff _ _ _).mp ((AffineCoset.eq_of_mem _ hy).trans (AffineCoset.eq_of_mem _ hx).symm)

lemma SlabKey.holes_unique (O : Finset A) (hP : F.SuccessfulSlabs O P)
    (k : F.SlabKey P j) {x y : A} (hxO : x ∈ O) (hyO : y ∈ O)
    (hx : x ∈ k.points F P j) (hy : y ∈ k.points F P j) : x=y := by
  by_contra hne
  let p : F.LocalHolePair O ⟨j,k.1⟩ := ⟨(⟨x,Finset.mem_inter.mpr ⟨hxO,k.2.property hx⟩⟩,
    ⟨y,Finset.mem_inter.mpr ⟨hyO,k.2.property hy⟩⟩),fun h => hne (congrArg Subtype.val h)⟩
  obtain ⟨z,hz⟩ := k.diff F P j hx hy
  have he : F.localHolePairVector O ⟨j,k.1⟩ p = (z.2,z.1.val) :=
    F.u_injective j ((F.localHolePairVector_eq O _ p).trans hz.symm)
  apply hP.holes _ p
  rw [he]
  exact z.1.property

end DirectionFrame
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
