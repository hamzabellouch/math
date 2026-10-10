import OAI.RingTheory.DirectFiniteness.AffineLines

namespace OAI

universe u_1 u_2 u_3 u_4

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q : Type u_1} {A : Type u_2} {B : Type u_3} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup B] [Module Q B] [Fintype Q] [Fintype A] [Fintype B]

omit [Fintype A] [Fintype B] in
lemma image_linePoints (f : B →ₗ[Q] A) (o x v : B) :
    (linePoints (Q := Q) x v).image (fun z => f (o+z)) =
      linePoints (Q := Q) (f (o+x)) (f v) := by
  ext y
  simp only [Finset.mem_image,mem_linePoints]
  constructor
  · rintro ⟨z,⟨t,rfl⟩,rfl⟩
    exact ⟨t,by simp [map_add,add_assoc]⟩
  · rintro ⟨t,rfl⟩
    exact ⟨x+t • v,⟨t,rfl⟩,by simp [map_add,add_assoc]⟩

omit [Fintype A] [Fintype B] in
lemma image_affine_linePoints (f : B →ₗ[Q] A) (o : A) (x v : B) :
    (linePoints (Q := Q) x v).image (fun z => o + f z) =
      linePoints (Q := Q) (o+f x) (f v) := by
  ext point
  constructor
  · intro membership
    obtain ⟨preimage, preimage_mem, rfl⟩ := Finset.mem_image.mp membership
    obtain ⟨scalar, rfl⟩ := (mem_linePoints _ _ _).mp preimage_mem
    exact (mem_linePoints _ _ _).mpr ⟨scalar, by simp only [map_add, map_smul, add_assoc]⟩
  · intro membership
    obtain ⟨scalar, rfl⟩ := (mem_linePoints _ _ _).mp membership
    exact Finset.mem_image.mpr ⟨x + scalar • v, (mem_linePoints _ _ _).mpr ⟨scalar, rfl⟩,
      by simp only [map_add, map_smul, add_assoc]⟩

omit [Fintype A] [Fintype B] in
lemma FullLine.image_affine {s : Finset B} (hs : FullLine (Q := Q) s)
    (f : B →ₗ[Q] A) (hf : Function.Injective f) (o : A) :
    FullLine (Q := Q) (s.image (fun z => o+f z)) := by
  obtain ⟨x,v,hv,rfl⟩ := hs
  rw [image_affine_linePoints]
  exact ⟨o+f x,f v,fun he => hv (hf (he.trans f.map_zero.symm)),rfl⟩

/-- A full-line partition of one finite affine slab. -/
structure PartitionOn (S : Finset A) where
  through : S → Finset A
  subset : ∀ x, through x ⊆ S
  self : ∀ x, x.val ∈ through x
  full : ∀ x, FullLine (Q := Q) (through x)
  stable : ∀ x y, y.val ∈ through x → through y = through x

namespace PartitionOn
variable (f : B →ₗ[Q] A) (hf : Function.Injective f) (o : A)

local instance identityRingHomSurjective : RingHomSurjective (RingHom.id Q) := inferInstance

def parametrization : B ≃ ↥(cosetPoints f.range o) :=
  Equiv.ofBijective (fun x => ⟨o+f x,by simp⟩) (by
    constructor
    · intro x y h; exact hf (add_left_cancel (congrArg Subtype.val h))
    · rintro ⟨y,hy⟩
      obtain ⟨x,hx⟩ := (mem_cosetPoints _ _ _).mp hy
      exact ⟨x,Subtype.ext (by change o+f x=y; rw [hx]; abel)⟩)

omit [Fintype Q] [Fintype B] in
@[simp] lemma parametrization_val (x : B) : (parametrization f hf o x).val = o+f x := rfl

omit [Fintype Q] [Fintype B] in
@[simp] lemma parametrization_symm_apply (x : ↥(cosetPoints f.range o)) :
    o+f ((parametrization f hf o).symm x)=x.val := by
  exact congrArg Subtype.val ((parametrization f hf o).apply_symm_apply x)

def image (L : LinePartition (Q := Q) (A := B)) : PartitionOn (Q := Q) (cosetPoints f.range o) where
  through x := (L.through ((parametrization f hf o).symm x)).image (fun z => o+f z)
  subset x := by
    rintro y hy
    obtain ⟨z,_,rfl⟩ := Finset.mem_image.mp hy
    simp
  self x := Finset.mem_image.mpr ⟨_,L.self _,parametrization_symm_apply f hf o x⟩
  full x := (L.full _).image_affine f hf o
  stable x y hy := by
    obtain ⟨z,hz,hzy⟩ := Finset.mem_image.mp hy
    have he : z=(parametrization f hf o).symm y := by
      apply (parametrization f hf o).injective
      apply Subtype.ext
      simpa using hzy
    rw [he] at hz
    rw [L.stable _ _ hz]

omit [Fintype B] in
lemma image_through (L : LinePartition (Q := Q) (A := B)) (x : B) :
    (image f hf o L).through (parametrization f hf o x) =
      (L.through x).image (fun z => o+f z) := by
  simp [image]

end PartitionOn

section Glue
variable {ι : Type u_4} (S : ι → Finset A) (key : A → ι)
  (hmem : ∀ x, x ∈ S (key x))
  (hkey : ∀ x y, y ∈ S (key x) → key y=key x)
  (L : ∀ i, PartitionOn (Q := Q) (S i))

def gluePartition : LinePartition (Q := Q) (A := A) where
  through x := (L (key x)).through ⟨x,hmem x⟩
  self x := (L (key x)).self ⟨x,hmem x⟩
  full x := (L (key x)).full ⟨x,hmem x⟩
  stable x y hy := by
    have hyS := (L (key x)).subset ⟨x,hmem x⟩ hy
    have he := hkey x y hyS
    have transport (i i' : ι) (heq : i=i') (hi : y ∈ S i) (hi' : y ∈ S i') :
        (L i).through ⟨y,hi⟩ = (L i').through ⟨y,hi'⟩ := by subst i'; rfl
    exact (transport _ _ he (hmem y) hyS).trans
      ((L (key x)).stable ⟨x,hmem x⟩ ⟨y,hyS⟩ hy)

end Glue
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
