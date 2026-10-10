import Mathlib
import OAI.SetTheory.PartitionConsistency.Algebra.GateTowers
import OAI.SetTheory.PartitionConsistency.Algebra.MergerCones

namespace OAI

/-! ## Base -/

namespace PartitionConsistency.MonoidConstruction
universe u
open DiagramOrder

/-- The objects used by the construction retain the real margin together with
an actual cancellative conical monoid; no saturation property is built in. -/
structure Object where
  Carrier : Type u
  [monoid : LeftCancelMonoid Carrier]
  [conical : IsConical Carrier]
  joins : HasConditionalJoins (LeftDivOrder Carrier)
  margin : HeightCost (LeftDivOrder Carrier)
  e : Carrier
  e_ne_one : e ≠ 1

instance : CoeSort Object (Type u) := ⟨Object.Carrier⟩
attribute [instance] Object.monoid Object.conical

namespace Base
abbrev M := Multiplicative ℕ

def degree (x : LeftDivOrder M) : ℕ := @Multiplicative.toAdd ℕ x

instance : IsConical M where
  eq_one_of_mul_eq_one {x y} h := by
    change degree x + degree y = 0 at h
    exact ⟨Nat.eq_zero_of_add_eq_zero_right h, Nat.eq_zero_of_add_eq_zero_left h⟩

theorem le_iff (x y : LeftDivOrder M) : x ≤ y ↔ degree x ≤ degree y := by
  change (∃ z : M, degree x + degree z = degree y) ↔ degree x ≤ degree y
  exact ⟨fun ⟨z,h⟩ => h ▸ Nat.le_add_right _ _,
    fun h => ⟨Multiplicative.ofAdd (degree y - degree x), Nat.add_sub_of_le h⟩⟩

theorem lt_iff (x y : LeftDivOrder M) : x < y ↔ degree x < degree y := by
  rw [lt_iff_le_not_ge, le_iff, le_iff, ← lt_iff_le_not_ge]

theorem joins : HasConditionalJoins (LeftDivOrder M) := by
  intro x y _ _ _
  refine ⟨(show LeftDivOrder M from @Multiplicative.ofAdd ℕ (max (degree x) (degree y))), ?_⟩
  apply (pair_lub_iff (α := LeftDivOrder M) _ _ _).2
  intro z
  rw [le_iff, le_iff, le_iff]
  exact max_le_iff.symm

noncomputable def height (x : LeftDivOrder M) : ℝ := 1 - (1/2:ℝ) ^ (degree x+1)
noncomputable def cost (x : LeftDivOrder M) : ℝ := (1/2:ℝ) ^ (degree x+3)

theorem height_pos (x : LeftDivOrder M) : 0 < height x := by
  have h : (1/2:ℝ) ^ (degree x+1) < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  exact sub_pos.mpr h

theorem height_lt_one (x : LeftDivOrder M) : height x < 1 := by
  have h : 0 < (1/2:ℝ) ^ (degree x+1) := pow_pos (by norm_num) _
  unfold height
  linarith

theorem margin {x y : LeftDivOrder M} (hxy : x < y) :
    UniformMargin height cost x y := by
  have hxy' := (lt_iff x y).1 hxy
  refine ⟨(1/2:ℝ) ^ (degree x+3), ?_, ?_⟩
  · have hp : (1/2:ℝ) ^ (degree y+1) ≤ (1/2:ℝ) ^ (degree x+2) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have hx : 0 < (1/2:ℝ) ^ (degree x+1) := pow_pos (by norm_num) _
    show (1/2:ℝ) ^ (degree x+3) <
      (1 - (1/2:ℝ) ^ (degree y+1)) - (1 - (1/2:ℝ) ^ (degree x+1))
    have he2 : (1/2:ℝ) ^ (degree x+2) = (1/2:ℝ) ^ (degree x+1) * (1/2) :=
      pow_succ _ _
    have he3 : (1/2:ℝ) ^ (degree x+3) = (1/2:ℝ) ^ (degree x+1) * (1/2) * (1/2) := by
      rw [pow_succ, he2]
    rw [he2] at hp
    rw [he3]
    nlinarith
  · intro d hd hdx
    have hx := (le_iff d x).not.1 hdx
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)

noncomputable def heightCost : HeightCost (LeftDivOrder M) where
  height := height
  cost := cost
  height_pos := height_pos
  height_lt_one := height_lt_one
  cost_pos _ := pow_pos (by norm_num) _
  cost_le_one _ := pow_le_one₀ (by norm_num) (by norm_num)
  margin hxy := (margin hxy).supremum_lt hxy

/-- The free monoid on one generator, with the source's concrete base heights. -/
noncomputable def object : Object.{0} where
  Carrier := M
  monoid := inferInstance
  conical := inferInstance
  joins := joins
  margin := heightCost
  e := Multiplicative.ofAdd 1
  e_ne_one := by decide

end Base
end PartitionConsistency.MonoidConstruction


/-! ## Operation -/

namespace PartitionConsistency.MonoidConstruction
universe u v
open DiagramOrder
noncomputable section

/-- The amount reserved by the margin at an ordered pair. -/
def missedSup (M : Object.{u}) (x y : M) : ℝ :=
  sSup (M.margin.cost '' {d : LeftDivOrder M | d ≤ y ∧ ¬ d ≤ x})

/-- Maps of construction stages retain right factors, disjointness, and
exact old suprema. Such maps make continuous unions legitimate stages. -/
structure Hom (M : Object.{u}) (N : Object.{v}) extends M →* N where
  conservative : Conservative toMonoidHom
  map_e : toMonoidHom M.e = N.e
  height : ∀ x, N.margin.height (toMonoidHom x) = M.margin.height x
  cost : ∀ x, N.margin.cost (toMonoidHom x) = M.margin.cost x
  supremum : ∀ x y, missedSup N (toMonoidHom x) (toMonoidHom y) = missedSup M x y

instance {M : Object.{u}} {N : Object.{v}} : CoeFun (Hom M N) (fun _ => M → N) :=
  ⟨fun f => f.toMonoidHom⟩

namespace Hom
universe w
variable {M : Object.{u}} {N : Object.{v}} {R : Object.{w}}

@[ext] theorem ext {f g : Hom M N} (h : ∀ x, f x = g x) : f = g := by
  cases f; cases g
  congr 1
  exact MonoidHom.ext h

def id (M : Object.{u}) : Hom M M where
  toMonoidHom := MonoidHom.id M
  conservative := Conservative.id M
  map_e := rfl
  height _ := rfl
  cost _ := rfl
  supremum _ _ := rfl

def comp (g : Hom N R) (f : Hom M N) : Hom M R where
  toMonoidHom := g.toMonoidHom.comp f.toMonoidHom
  conservative := f.conservative.comp g.conservative
  map_e := by change g (f M.e) = R.e; rw [f.map_e, g.map_e]
  height x := (g.height (f x)).trans (f.height x)
  cost x := (g.cost (f x)).trans (f.cost x)
  supremum x y := (g.supremum (f x) (f y)).trans (f.supremum x y)

@[simp] theorem id_apply (x : M) : (id M) x = x := rfl
@[simp] theorem comp_apply (g : Hom N R) (f : Hom M N) (x : M) :
    (g.comp f) x = g (f x) := rfl

@[simp] theorem id_comp (f : Hom M N) : (id N).comp f = f := by ext; rfl
@[simp] theorem comp_id (f : Hom M N) : f.comp (id M) = f := by ext; rfl

theorem injective (f : Hom M N) : Function.Injective f := f.conservative.injective

end Hom

/-- A probe request has exactly the old parameters in the presentation;
its path contains its countably many transition and terminal quotients by
conservativity, not an additional saturation assumption. -/
structure ProbeData (M : Object.{u}) where
  a : M
  b : M
  b_ne_one : b ≠ 1
  path : ProbeAlgebra.Path M a

namespace ProbeData
variable {M : Object.{u}} (d : ProbeData M)

/-- Executing a request uses the established literal normal forms. -/
def extension : Object.{u} where
  Carrier := d.path.Extension M.e_ne_one d.b
  monoid := inferInstance
  conical := inferInstance
  joins := d.path.extension_hasConditionalJoins M.e_ne_one d.b M.joins d.b_ne_one
  margin := d.path.extensionHeightCost M.e_ne_one d.b d.b_ne_one M.margin M.joins
  e := ProbeAlgebra.Word.old (d.path.alphabet M.e_ne_one) d.b M.e
  e_ne_one he := M.e_ne_one
    ((d.path.oldHom_conservative M.e_ne_one d.b).injective he)

def inclusion : Hom M d.extension where
  toMonoidHom := ProbeAlgebra.Word.oldHom (d.path.alphabet M.e_ne_one) d.b
  conservative := d.path.oldHom_conservative M.e_ne_one d.b
  map_e := rfl
  height _ := rfl
  cost _ := rfl
  supremum := d.path.extension_old_cost_supremum M.e_ne_one d.b d.b_ne_one M.margin M.joins

def probe : d.extension := d.path.probe M.e_ne_one d.b d.b_ne_one 0

theorem profile : ProbeProfile (d.inclusion d.a) (d.inclusion d.b) d.extension.e
    d.probe (fun i => d.inclusion (d.path.node i)) :=
  d.path.probeProfile M.e_ne_one d.b M.joins d.b_ne_one

theorem probe_new : ¬ ∃ x : M, d.inclusion x = d.probe := by
  rintro ⟨x,hx⟩
  have h : ProbeAlgebra.Raw.old x =
    ProbeAlgebra.Raw.cons (d.path.letter 0 1) (.old 1) := congrArg Subtype.val hx
  cases h

theorem gates : HasOldGates d.inclusion.toMonoidHom :=
  d.path.hasOldGates M.e_ne_one d.b M.joins

theorem cardinal_le {μ : Cardinal.{u}} (hω : Cardinal.aleph0 ≤ μ)
    (hM : Cardinal.mk M ≤ μ) : Cardinal.mk d.extension ≤ μ :=
  d.path.extension_cardinal_le M.e_ne_one d.b hω hM

/-- Later probes preserve the full previous profile, including their own
new divisors of the upper bound. -/
theorem preserves_profile {a b e m : M} {n : ℕ → M} (h : ProbeProfile a b e m n) :
    ProbeProfile (d.inclusion a) (d.inclusion b) (d.inclusion e)
      (d.inclusion m) (fun k => d.inclusion (n k)) :=
  h.map d.inclusion.conservative d.gates

end ProbeData

structure MergerData (M : Object.{u}) where
  n : ℕ
  positive : 0 < n
  prescription : DiagramForcing.OverlapPrescription M n
  valid : prescription.Valid

namespace MergerData
variable {M : Object.{u}} (d : MergerData M)

def extension : Object.{u} where
  Carrier := d.prescription.Merger d.valid
  monoid := inferInstance
  conical := inferInstance
  joins := d.prescription.merger_hasConditionalJoins d.valid M.joins
  margin := d.prescription.mergerHeightCost d.valid M.margin d.positive
  e := .old M.e
  e_ne_one he := M.e_ne_one
    ((MergerAlgebra.Word.oldHom_conservative).injective he)

def inclusion : Hom M d.extension where
  toMonoidHom := MergerAlgebra.Word.oldHom
  conservative := MergerAlgebra.Word.oldHom_conservative
  map_e := rfl
  height _ := rfl
  cost _ := rfl
  supremum := d.prescription.merger_old_cost_supremum d.valid M.margin d.positive

def root (i : Fin d.n) : d.extension := d.prescription.root d.valid i

theorem realization (z w : Fin d.n × M) :
    d.root z.1 * d.inclusion z.2 = d.root w.1 * d.inclusion w.2 ↔
      d.prescription.Rel z w :=
  d.prescription.root_mul_eq_iff d.valid z w

theorem no_new_old_divisors (w : d.extension) (a : M) (h : w ∣ d.inclusion a) :
    ∃ x : M, d.inclusion x = w := by
  rcases MergerAlgebra.Word.hasOldGates w ⟨a,h⟩ with h | ⟨g,hg⟩
  · exact h
  · obtain ⟨z,hz⟩ := hg.divides
    obtain ⟨x,_,hx,_,_⟩ := MergerAlgebra.Word.factors_of_old hz.symm
    exact ⟨x,hx.symm⟩

theorem gates : HasOldGates d.inclusion.toMonoidHom :=
  MergerAlgebra.Word.hasOldGates

theorem cardinal_le {μ : Cardinal.{u}} (hω : Cardinal.aleph0 ≤ μ)
    (hM : Cardinal.mk M ≤ μ) : Cardinal.mk d.extension ≤ μ :=
  d.prescription.merger_cardinal_le d.valid hω hM

theorem preserves_profile {a b e m : M} {n : ℕ → M} (h : ProbeProfile a b e m n) :
    ProbeProfile (d.inclusion a) (d.inclusion b) (d.inclusion e)
      (d.inclusion m) (fun k => d.inclusion (n k)) :=
  h.map d.inclusion.conservative d.gates

end MergerData
end
end PartitionConsistency.MonoidConstruction

end OAI
