import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundMainStageFromCodes

namespace OAI

section

namespace PartitionPilot.Forcing.InitialMainAlgebra
universe u

def carrier : ZFSet.{u} := natSetCode 2
def actors : ZFSet.{u} := natSetCode 1
def bottom : ZFSet.{u} := natSetCode 0
def top : ZFSet.{u} := natSetCode 1
def identity : ZFSet.{u} := bottom
def order : ZFSet.{u} :=
  {ZFSet.pair bottom bottom, ZFSet.pair bottom top, ZFSet.pair top top}
def meetGraph : ZFSet.{u} :=
  {ZFSet.pair (ZFSet.pair bottom bottom) bottom,
    ZFSet.pair (ZFSet.pair bottom top) bottom,
    ZFSet.pair (ZFSet.pair top bottom) bottom,
    ZFSet.pair (ZFSet.pair top top) top}
def multiplication : ZFSet.{u} := {ZFSet.pair (ZFSet.pair identity identity) identity}
def inverse : ZFSet.{u} := {ZFSet.pair identity identity}
def action : ZFSet.{u} :=
  {ZFSet.pair (ZFSet.pair identity bottom) bottom, ZFSet.pair (ZFSet.pair identity top) top}

theorem bottom_ne_top : (bottom : ZFSet.{u}) ≠ top := by
  intro equal
  have := natSetCode_injective equal
  exact Nat.zero_ne_one this

theorem mem_carrier (x : ZFSet.{u}) : x ∈ carrier ↔ x = bottom ∨ x = top := by
  change x ∈ insert (natSetCode 1) (insert (natSetCode 0) ∅) ↔ _
  simp only [ZFSet.mem_insert_iff, ZFSet.notMem_empty, or_false]
  exact or_comm

theorem mem_actors (x : ZFSet.{u}) : x ∈ actors ↔ x = identity := by
  change x ∈ insert (natSetCode 0) ∅ ↔ _
  simp only [ZFSet.mem_insert_iff, ZFSet.notMem_empty, or_false]
  rfl

theorem bottom_mem : (bottom : ZFSet.{u}) ∈ carrier := (mem_carrier _).2 (Or.inl rfl)
theorem top_mem : (top : ZFSet.{u}) ∈ carrier := (mem_carrier _).2 (Or.inr rfl)
theorem identity_mem : (identity : ZFSet.{u}) ∈ actors := (mem_actors _).2 rfl

theorem pair_mem_order (x y : ZFSet.{u}) : ZFSet.pair x y ∈ order ↔
    (x = bottom ∧ y = bottom) ∨ (x = bottom ∧ y = top) ∨ (x = top ∧ y = top) := by
  simp only [order, ZFSet.mem_insert_iff, ZFSet.mem_singleton, ZFSet.pair_inj]

theorem pair_mem_meetGraph (x y z : ZFSet.{u}) : ZFSet.pair (ZFSet.pair x y) z ∈ meetGraph ↔
    ((x = bottom ∧ y = bottom) ∧ z = bottom) ∨
      ((x = bottom ∧ y = top) ∧ z = bottom) ∨
        ((x = top ∧ y = bottom) ∧ z = bottom) ∨ ((x = top ∧ y = top) ∧ z = top) := by
  simp only [meetGraph, ZFSet.mem_insert_iff, ZFSet.mem_singleton, ZFSet.pair_inj]

theorem pair_mem_multiplication (x y z : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair x y) z ∈ multiplication ↔ (x = identity ∧ y = identity) ∧ z = identity := by
  simp only [multiplication, ZFSet.mem_singleton, ZFSet.pair_inj]

theorem pair_mem_inverse (x y : ZFSet.{u}) : ZFSet.pair x y ∈ inverse ↔ x = identity ∧ y = identity := by
  simp only [inverse, ZFSet.mem_singleton, ZFSet.pair_inj]

theorem pair_mem_action (g x y : ZFSet.{u}) : ZFSet.pair (ZFSet.pair g x) y ∈ action ↔
    ((g = identity ∧ x = bottom) ∧ y = bottom) ∨ ((g = identity ∧ x = top) ∧ y = top) := by
  simp only [action, ZFSet.mem_pair, ZFSet.pair_inj]

theorem least (x : ZFSet.{u}) (hx : x ∈ carrier) : ZFSet.pair bottom x ∈ order := by
  rcases (mem_carrier x).1 hx with rfl | rfl <;> simp [pair_mem_order]

theorem greatest (x : ZFSet.{u}) (hx : x ∈ carrier) : ZFSet.pair x top ∈ order := by
  rcases (mem_carrier x).1 hx with rfl | rfl <;> simp [pair_mem_order]

theorem meet_function : ZFSet.IsFunc (ZFSet.prod carrier carrier) carrier (meetGraph : ZFSet.{u}) := by
  constructor
  · intro z hz
    simp only [meetGraph, ZFSet.mem_insert_iff, ZFSet.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨bottom_mem, bottom_mem⟩, bottom_mem⟩
    · exact ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨bottom_mem, top_mem⟩, bottom_mem⟩
    · exact ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨top_mem, bottom_mem⟩, bottom_mem⟩
    · exact ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨top_mem, top_mem⟩, top_mem⟩
  · intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 hz
    rcases (mem_carrier x).1 hx with rfl | rfl <;>
      rcases (mem_carrier y).1 hy with rfl | rfl <;>
        simp [pair_mem_meetGraph, bottom_ne_top, Ne.symm bottom_ne_top]

theorem meet_code : MeetOrderCode carrier order (meetGraph : ZFSet.{u}) where
  order := {
    relation := by
      intro z hz
      simp only [order, ZFSet.mem_insert_iff, ZFSet.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl <;> simp [mem_carrier]
    refl := by
      intro x hx
      rcases (mem_carrier x).1 hx with rfl | rfl <;> simp [pair_mem_order]
    antisymm := by
      intro x hx y hy xy yx
      rcases (mem_carrier x).1 hx with rfl | rfl <;>
        rcases (mem_carrier y).1 hy with rfl | rfl <;>
          simp_all [pair_mem_order, bottom_ne_top, Ne.symm bottom_ne_top]
    trans := by
      intro x hx y hy z hz xy yz
      rcases (mem_carrier x).1 hx with rfl | rfl <;>
        rcases (mem_carrier y).1 hy with rfl | rfl <;>
          rcases (mem_carrier z).1 hz with rfl | rfl <;>
            simp_all [pair_mem_order, bottom_ne_top, Ne.symm bottom_ne_top] }
  operation := meet_function
  lower_left := by
    intro x y z entry
    rcases (pair_mem_meetGraph x y z).1 entry with
      ⟨⟨rfl, rfl⟩, rfl⟩ | ⟨⟨rfl, rfl⟩, rfl⟩ | ⟨⟨rfl, rfl⟩, rfl⟩ | ⟨⟨rfl, rfl⟩, rfl⟩ <;>
        simp [pair_mem_order]
  lower_right := by
    intro x y z entry
    rcases (pair_mem_meetGraph x y z).1 entry with
      ⟨⟨rfl, rfl⟩, rfl⟩ | ⟨⟨rfl, rfl⟩, rfl⟩ | ⟨⟨rfl, rfl⟩, rfl⟩ | ⟨⟨rfl, rfl⟩, rfl⟩ <;>
        simp [pair_mem_order]
  greatest := by
    intro x y z w hw entry wx wy
    rcases (pair_mem_meetGraph x y z).1 entry with
      ⟨⟨rfl, rfl⟩, rfl⟩ | ⟨⟨rfl, rfl⟩, rfl⟩ | ⟨⟨rfl, rfl⟩, rfl⟩ | ⟨⟨rfl, rfl⟩, rfl⟩ <;>
        rcases (mem_carrier w).1 hw with rfl | rfl <;>
          simp_all [pair_mem_order, bottom_ne_top, Ne.symm bottom_ne_top]

theorem group_code : GroupCode actors multiplication inverse (identity : ZFSet.{u}) where
  mul_function := by
    constructor
    · intro z hz
      rw [multiplication, ZFSet.mem_singleton] at hz
      rw [hz]
      simp [mem_actors]
    · intro z hz
      obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 hz
      obtain rfl := (mem_actors x).1 hx
      obtain rfl := (mem_actors y).1 hy
      simp [pair_mem_multiplication]
  inv_function := by
    constructor
    · intro z hz
      rw [inverse, ZFSet.mem_singleton] at hz
      rw [hz]
      simp [mem_actors]
    · intro x hx
      obtain rfl := (mem_actors x).1 hx
      simp [pair_mem_inverse]
  identity_mem := identity_mem
  one_mul := by
    intro x hx
    obtain rfl := (mem_actors x).1 hx
    simp [pair_mem_multiplication]
  mul_one := by
    intro x hx
    obtain rfl := (mem_actors x).1 hx
    simp [pair_mem_multiplication]
  inv_mul := by
    intro x hx y hy entry
    obtain rfl := (mem_actors x).1 hx
    obtain rfl := (mem_actors y).1 hy
    simp [pair_mem_multiplication]
  mul_assoc := by
    intro x hx y hy z hz a ha b hb c hc xy yz az
    obtain rfl := (mem_actors x).1 hx
    obtain rfl := (mem_actors y).1 hy
    obtain rfl := (mem_actors z).1 hz
    obtain rfl := (mem_actors a).1 ha
    obtain rfl := (mem_actors b).1 hb
    obtain rfl := (mem_actors c).1 hc
    simp [pair_mem_multiplication]

theorem action_code : PosetActionCode actors carrier multiplication identity order (action : ZFSet.{u}) where
  function := by
    constructor
    · intro z hz
      simp only [action, ZFSet.mem_pair] at hz
      rcases hz with rfl | rfl <;> simp [mem_actors, mem_carrier]
    · intro z hz
      obtain ⟨g, hg, x, hx, rfl⟩ := ZFSet.mem_prod.1 hz
      obtain rfl := (mem_actors g).1 hg
      rcases (mem_carrier x).1 hx with rfl | rfl <;>
        simp [pair_mem_action, bottom_ne_top, Ne.symm bottom_ne_top]
  one := by
    intro x hx
    rcases (mem_carrier x).1 hx with rfl | rfl <;> simp [pair_mem_action]
  mul := by
    intro g hg h hh k hk x hx y hy z hz gh hxY gyZ
    obtain rfl := (mem_actors g).1 hg
    obtain rfl := (mem_actors h).1 hh
    obtain rfl := (mem_actors k).1 hk
    rcases (pair_mem_action identity x y).1 hxY with ⟨⟨_, rfl⟩, rfl⟩ | ⟨⟨_, rfl⟩, rfl⟩ <;>
      simpa only using gyZ
  monotone := by
    intro g hg x hx y hy z hz w hw gxZ gyW xy
    rcases (pair_mem_action g x z).1 gxZ with ⟨⟨rfl, rfl⟩, rfl⟩ | ⟨⟨rfl, rfl⟩, rfl⟩ <;>
      rcases (pair_mem_action identity y w).1 gyW with ⟨⟨_, rfl⟩, rfl⟩ | ⟨⟨_, rfl⟩, rfl⟩ <;>
        exact xy

end PartitionPilot.Forcing.InitialMainAlgebra

end

end OAI
