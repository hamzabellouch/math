import OAI.Topology.ArtinGroups.DeligneDefinitions

namespace OAI

/-!
# Parabolic subgroups for result 082-03

We use the Artin presentation and standard parabolics already used by
`Topology.ArtinGroups`. In Mathlib's Coxeter matrix convention, a zero
off-diagonal entry means an infinite label.
-/

namespace HarmonicArtin.ParabolicIntersections

variable {G : Type*} [Group G]

/-- `g P g⁻¹`, with membership expressed without existential witnesses. -/
def conjugate (g : G) (P : Subgroup G) : Subgroup G :=
  P.comap (MulAut.conj g⁻¹).toMonoidHom

@[simp] theorem mem_conjugate (g : G) (P : Subgroup G) (a : G) :
    a ∈ conjugate g P ↔ g⁻¹ * a * g ∈ P := by
  simp [conjugate]

@[simp] theorem conjugate_one (P : Subgroup G) : conjugate 1 P = P := by
  ext a
  simp

@[simp] theorem conjugate_top (g : G) : conjugate g (⊤ : Subgroup G) = ⊤ := by
  ext a
  simp

@[simp] theorem conjugate_bot (g : G) : conjugate g (⊥ : Subgroup G) = ⊥ := by
  ext a
  simp only [mem_conjugate, Subgroup.mem_bot]
  constructor
  · intro h
    calc
      a = g * (g⁻¹ * a * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; simp
  · rintro rfl
    simp

theorem conjugate_mul (g h : G) (P : Subgroup G) :
    conjugate (g * h) P = conjugate g (conjugate h P) := by
  ext a
  simp only [mem_conjugate, mul_inv_rev]
  group

@[simp] theorem conjugate_inv_cancel (g : G) (P : Subgroup G) :
    conjugate g⁻¹ (conjugate g P) = P := by
  rw [← conjugate_mul, inv_mul_cancel, conjugate_one]

theorem conjugate_mono (g : G) {P Q : Subgroup G} (h : P ≤ Q) :
    conjugate g P ≤ conjugate g Q := fun _ ha => h ha

@[simp] theorem conjugate_le_conjugate_iff (g : G) (P Q : Subgroup G) :
    conjugate g P ≤ conjugate g Q ↔ P ≤ Q := by
  constructor
  · intro h
    simpa using conjugate_mono g⁻¹ h
  · exact conjugate_mono g

theorem conjugate_inf (g : G) (P Q : Subgroup G) :
    conjugate g (P ⊓ Q) = conjugate g P ⊓ conjugate g Q := rfl

/-- Conjugation as an order isomorphism of the subgroup lattice. -/
def conjugateOrderIso (g : G) : Subgroup G ≃o Subgroup G where
  toFun := conjugate g
  invFun := conjugate g⁻¹
  left_inv := conjugate_inv_cancel g
  right_inv P := by simpa using conjugate_inv_cancel g⁻¹ P
  map_rel_iff' := fun {P Q} => conjugate_le_conjugate_iff g P Q

theorem conjugate_sup (g : G) (P Q : Subgroup G) :
    conjugate g (P ⊔ Q) = conjugate g P ⊔ conjugate g Q :=
  (conjugateOrderIso g).map_sup P Q

theorem conjugate_eq_self {g : G} {P : Subgroup G} (hg : g ∈ P) :
    conjugate g P = P := by
  ext a
  rw [mem_conjugate]
  constructor
  · intro ha
    have hb := P.mul_mem (P.mul_mem hg ha) (P.inv_mem hg)
    simpa [mul_assoc] using hb
  · intro ha
    exact P.mul_mem (P.mul_mem (P.inv_mem hg) ha) hg

variable {S : Type*} (M : CoxeterMatrix S)

/-- Conjugates of standard subgroups, with no spherical-type restriction. -/
def IsParabolic (P : Subgroup (Artin M)) : Prop :=
  ∃ (X : Set S) (g : Artin M), P = conjugate g (artinParabolic M X)

theorem standard_isParabolic (X : Set S) : IsParabolic M (artinParabolic M X) :=
  ⟨X, 1, (conjugate_one _).symm⟩

theorem isParabolic_conjugate {P : Subgroup (Artin M)} (hP : IsParabolic M P)
    (g : Artin M) : IsParabolic M (conjugate g P) := by
  obtain ⟨X, h, rfl⟩ := hP
  exact ⟨X, g * h, (conjugate_mul g h _).symm⟩

theorem standard_univ : artinParabolic M Set.univ = ⊤ := by
  rw [artinParabolic, Set.image_univ]
  exact PresentedGroup.closure_range_of (braidRelators M)

theorem standard_mono {X Y : Set S} (h : X ⊆ Y) :
    artinParabolic M X ≤ artinParabolic M Y :=
  Subgroup.closure_mono (Set.image_mono h)

theorem standard_union (X Y : Set S) :
    artinParabolic M (X ∪ Y) = artinParabolic M X ⊔ artinParabolic M Y := by
  simp only [artinParabolic, Set.image_union, Subgroup.closure_union]

theorem top_isParabolic : IsParabolic M ⊤ := by
  rw [← standard_univ M]
  exact standard_isParabolic M Set.univ

end HarmonicArtin.ParabolicIntersections

end OAI
