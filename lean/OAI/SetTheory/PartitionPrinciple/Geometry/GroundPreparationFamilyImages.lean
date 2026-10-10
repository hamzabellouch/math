import OAI.SetTheory.PartitionPrinciple.Definability.ExternalTileSlotSupportRealization
import OAI.SetTheory.PartitionPrinciple.Definability.GroundDepthSlotCodes

namespace OAI

namespace PartitionPilot.Forcing
open SetFormula
universe u
namespace BoundedFormula

def leastSlotFormula {n} (supports v x j : Fin n) : BoundedFormula n :=
  .conj (tripleMembershipFormula v j x supports)
    (allMem j (.neg (tripleMembershipFormula v.succ 0 x.succ supports.succ)))

theorem truth_leastSlotFormula {n} (supports v x j : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (leastSlotFormula supports v x j) env ↔
      LeastSlotCode (env supports) (env v) (env x) (env j) := by
  simp only [leastSlotFormula, Truth, truth_tripleMembershipFormula]
  rfl

def leastSlotOwnerEntryFormula {n} (z P B V owner supports three : Fin n) : BoundedFormula n :=
  exMem B (exMem three.succ (exMem V.succ.succ
    (.conj (orderedPairFormula z.succ.succ.succ 2 1)
      (.conj (.neg (.mem 2 P.succ.succ.succ))
        (.conj (pairMembershipFormula 2 0 owner.succ.succ.succ)
          (leastSlotFormula supports.succ.succ.succ 0 2 1))))))

theorem truth_leastSlotOwnerEntryFormula {n} (z P B V owner supports three : Fin n)
    (env : Fin n → ZFSet.{u}) (threeEq : env three = natSetCode 3) :
    Truth (leastSlotOwnerEntryFormula z P B V owner supports three) env ↔
      env z ∈ leastSlotOwnerGraph (env P) (env B) (env V) (env owner) (env supports) := by
  simp only [leastSlotOwnerEntryFormula, truth_exMem, Truth, truth_orderedPairFormula,
    truth_pairMembershipFormula, truth_leastSlotFormula]
  simp only [extend, Fin.cases_zero, Fin.cases_succ]
  rw [threeEq, leastSlotOwnerGraph, ZFSet.mem_sep]
  refine ⟨fun h => ⟨?_, h⟩, And.right⟩
  obtain ⟨x, hx, j, hj, _, _, equal, _⟩ := h
  rw [equal]
  exact ZFSet.pair_mem_prod.2 ⟨hx, hj⟩

end BoundedFormula
namespace TransitiveGround

theorem leastSlotOwnerGraph_mem (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {P B V owner supports : ZFSet.{u}} (hP : P ∈ M.sets) (hB : B ∈ M.sets)
    (hV : V ∈ M.sets) (hOwner : owner ∈ M.sets) (hSupports : supports ∈ M.sets) :
    leastSlotOwnerGraph P B V owner supports ∈ M.sets := by
  have hThree := M.natSetCode_mem separation infinite 3
  let params := extend P (extend B (extend V (extend owner (extend supports (extend (natSetCode 3) Fin.elim0)))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.leastSlotOwnerEntryFormula 0 1 2 3 4 5 6) params
    (Fin.cases hP (Fin.cases hB (Fin.cases hV (Fin.cases hOwner
      (Fin.cases hSupports (Fin.cases hThree (fun i => Fin.elim0 i)))))))
    (M.prod_mem pairing unions powers separation hB hThree)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.leastSlotOwnerEntryFormula 0 1 2 3 4 5 6) (extend z params))
      (ZFSet.prod B (natSetCode 3)) = leastSlotOwnerGraph P B V owner supports := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, BoundedFormula.truth_leastSlotOwnerEntryFormula _ _ _ _ _ _ _ _ rfl]
    exact ⟨And.right, fun h => ⟨(ZFSet.mem_sep.1 h).1, h⟩⟩
  exact equal ▸ selected

end TransitiveGround
end PartitionPilot.Forcing

section

namespace PartitionPilot.Forcing.GroundCompressionCompletion
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ : ZFSet.{u}}
variable (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)
noncomputable def externalOwnerSlots (P r μ A : ZFSet.{u}) : ZFSet.{u} :=
  leastSlotOwnerGraph (completion.externalSeedCarrier P r μ A)
    (completion.externalPointCarrier P r μ A)
    (M.externalStarVertices G (externalChildLetters I P (externalRectangles P G r μ A))
      (externalRequestCarrier I P (externalRectangles P G r μ A)) m one)
    (completion.externalStarOwner P r μ A) (completion.externalTileSlotPoints P r μ A)

end PartitionPilot.Forcing.GroundCompressionCompletion

namespace PartitionPilot.Forcing.GroundExternalGeometryInputs
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets)
local notation "P" => completion.externalSeedCarrier P0 r0 μ0 A0
local notation "B" => completion.externalPointCarrier P0 r0 μ0 A0
local notation "letters" => externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)
local notation "requests" => externalRequestCarrier I P0 (externalRectangles P0 G r0 μ0 A0)
local notation "slots" => completion.externalOwnerSlots P0 r0 μ0 A0
include data group oldAction pairing unions powers separation infinite hG

theorem externalSeedCarrier_ground (hP0 : P0 ∈ M.sets) : P ∈ M.sets := by
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP0
  exact M.relationImage_mem separation (completion.algebra.union.ground 0) geometry.carrier_ground
    (geometry.copies_ground _ data.group.group_code.identity_mem)

theorem externalOwnerSlots_ground_function (hP0 : P0 ∈ M.sets) :
    slots ∈ M.sets ∧ ZFSet.IsFunc (ownerFresh P B) (natSetCode 3) slots := by
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP0
  have owner := data.externalStarOwner_ground_function group oldAction pairing unions powers separation infinite hG hP0
  refine ⟨M.leastSlotOwnerGraph_mem pairing unions powers separation infinite
    (data.externalSeedCarrier_ground group oldAction pairing unions powers separation infinite hG hP0)
    geometry.carrier_ground (data.externalStarCarriers_ground pairing unions powers separation hG).1 owner.1
    (data.externalTileSlotPoints_ground group oldAction pairing unions powers separation infinite hG hP0), ?_⟩
  apply leastSlotOwnerGraph_function owner.2
  intro x _ fresh v owned
  exact data.externalTileSlotPoints_owner_cover group oldAction pairing unions powers separation infinite hG fresh owned

theorem externalOwnerSlots_monotone (hP0 : P0 ∈ M.sets) {x y v w n j k : ZFSet.{u}}
    (lower : ZFSet.pair x y ∈ completion.externalPointOrder P0 r0 μ0 A0)
    (firstOwner : ZFSet.pair x v ∈ completion.externalStarOwner P0 r0 μ0 A0)
    (secondOwner : ZFSet.pair y w ∈ completion.externalStarOwner P0 r0 μ0 A0)
    (firstDepth : ZFSet.pair v n ∈ M.externalStarDepth G letters requests m one)
    (secondDepth : ZFSet.pair w n ∈ M.externalStarDepth G letters requests m one)
    (first : ZFSet.pair x j ∈ slots) (second : ZFSet.pair y k ∈ slots) : j = k ∨ j ∈ k := by
  apply leastSlotOwnerGraph_monotone first second
  · intro v' w' ownedX ownedY
    have function := (data.externalStarOwner_ground_function group oldAction pairing unions powers separation infinite hG hP0).2
    have unique : FunctionGraphOn B (completion.externalStarOwner P0 r0 μ0 A0) := ⟨_, function⟩
    have vx := unique.unique ownedX firstOwner
    have wy := unique.unique ownedY secondOwner
    subst v'
    subst w'
    exact (data.externalStarOwner_order group oldAction pairing unions powers separation infinite hG
      lower firstOwner secondOwner firstDepth secondDepth).2 rfl
  · intro v _ j _ x hx y _ lower supported
    exact data.externalTileSlotPoints_lower group oldAction pairing unions powers separation infinite hG hx lower supported
  · exact lower

end PartitionPilot.Forcing.GroundExternalGeometryInputs

end

namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

theorem pairedGraph_function_of_subset {A B H K f g : ZFSet.{u}}
    (first : ZFSet.IsFunc A H f) (second : ZFSet.IsFunc B K g) (subset : B ⊆ A) :
    ZFSet.IsFunc B (ZFSet.prod H K) (pairedGraph B H K f g) := by
  refine ⟨fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_⟩
  intro x hx
  obtain ⟨a, firstEntry, firstUnique⟩ := first.2 x (subset hx)
  obtain ⟨b, secondEntry, secondUnique⟩ := second.2 x hx
  have ha := (ZFSet.pair_mem_prod.1 (first.1 firstEntry)).2
  have hb := (ZFSet.pair_mem_prod.1 (second.1 secondEntry)).2
  refine ⟨ZFSet.pair a b, (pair_mem_pairedGraph _ _ _ _ _ _ _ _).2
    ⟨hx, ha, hb, firstEntry, secondEntry⟩, ?_⟩
  intro y hy
  obtain ⟨x', _, a', _, b', _, equal, firstEntry', secondEntry'⟩ := (mem_pairedGraph _ _ _ _ _ _).1 hy
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
  exact congrArg₂ ZFSet.pair (firstUnique a' firstEntry') (secondUnique b' secondEntry')

namespace GroundCompressionCompletion
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ : ZFSet.{u}}
variable (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)

noncomputable def externalOwnerDepth (P r μ A : ZFSet.{u}) : ZFSet.{u} :=
  let letters := externalChildLetters I P (externalRectangles P G r μ A)
  let requests := externalRequestCarrier I P (externalRectangles P G r μ A)
  relationCompose (completion.externalPointCarrier P r μ A)
    (M.externalStarVertices G letters requests m one) ZFSet.omega
    (completion.externalStarOwner P r μ A) (M.externalStarDepth G letters requests m one)

noncomputable def externalOwnerLevelPairs (P r μ A : ZFSet.{u}) : ZFSet.{u} :=
  pairedGraph (ownerFresh (completion.externalSeedCarrier P r μ A) (completion.externalPointCarrier P r μ A))
    ZFSet.omega (natSetCode 3) (completion.externalOwnerDepth P r μ A) (completion.externalOwnerSlots P r μ A)

noncomputable def externalOwnerLevels (P r μ A : ZFSet.{u}) : ZFSet.{u} :=
  relationCompose (ownerFresh (completion.externalSeedCarrier P r μ A) (completion.externalPointCarrier P r μ A))
    (ZFSet.prod ZFSet.omega (natSetCode 3)) ZFSet.omega
    (completion.externalOwnerLevelPairs P r μ A) depthSlotGraph
end GroundCompressionCompletion

namespace GroundExternalGeometryInputs
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets)
local notation "P" => completion.externalSeedCarrier P0 r0 μ0 A0
local notation "B" => completion.externalPointCarrier P0 r0 μ0 A0
local notation "F" => ownerFresh P B
local notation "letters" => externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)
local notation "requests" => externalRequestCarrier I P0 (externalRectangles P0 G r0 μ0 A0)
local notation "V" => M.externalStarVertices G letters requests m one
local notation "owners" => completion.externalStarOwner P0 r0 μ0 A0
local notation "depths" => M.externalStarDepth G letters requests m one
local notation "ownerDepth" => completion.externalOwnerDepth P0 r0 μ0 A0
local notation "slots" => completion.externalOwnerSlots P0 r0 μ0 A0
local notation "pairs" => completion.externalOwnerLevelPairs P0 r0 μ0 A0
local notation "levels" => completion.externalOwnerLevels P0 r0 μ0 A0
include data group oldAction pairing unions powers separation infinite hG

theorem externalOwnerDepth_ground_function (hP0 : P0 ∈ M.sets) :
    ownerDepth ∈ M.sets ∧ ZFSet.IsFunc B ZFSet.omega ownerDepth := by
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP0
  have owner := data.externalStarOwner_ground_function group oldAction pairing unions powers separation infinite hG hP0
  have depth := data.externalStarDepth_ground_function group oldAction pairing unions powers separation infinite hG
  exact ⟨M.relationCompose_mem pairing unions powers separation geometry.carrier_ground
    (data.externalStarCarriers_ground pairing unions powers separation hG).1
    (M.omega_mem separation infinite) owner.1 depth.1,
    relationCompose_function_of_subset owner.2 depth.2 (fun _ h => h)⟩

theorem externalOwnerLevelPairs_ground_function (hP0 : P0 ∈ M.sets) :
    pairs ∈ M.sets ∧ ZFSet.IsFunc F (ZFSet.prod ZFSet.omega (natSetCode 3)) pairs := by
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP0
  have depth := data.externalOwnerDepth_ground_function group oldAction pairing unions powers separation infinite hG hP0
  have slot := data.externalOwnerSlots_ground_function group oldAction pairing unions powers separation infinite hG hP0
  exact ⟨M.pairedGraph_mem pairing unions powers separation
    (M.ownerFresh_mem separation
      (data.externalSeedCarrier_ground group oldAction pairing unions powers separation infinite hG hP0) geometry.carrier_ground)
    (M.omega_mem separation infinite) (M.natSetCode_mem separation infinite 3) depth.1 slot.1,
    pairedGraph_function_of_subset depth.2 slot.2 (fun x h => ((mem_ownerFresh P B x).1 h).1)⟩

theorem externalOwnerLevels_ground_function (hP0 : P0 ∈ M.sets) :
    levels ∈ M.sets ∧ ZFSet.IsFunc F ZFSet.omega levels := by
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP0
  have pairCode := data.externalOwnerLevelPairs_ground_function group oldAction pairing unions powers separation infinite hG hP0
  have hOmega := M.omega_mem separation infinite
  exact ⟨M.relationCompose_mem pairing unions powers separation
    (M.ownerFresh_mem separation
      (data.externalSeedCarrier_ground group oldAction pairing unions powers separation infinite hG hP0) geometry.carrier_ground)
    (M.prod_mem pairing unions powers separation hOmega (M.natSetCode_mem separation infinite 3)) hOmega
    pairCode.1 (M.depthSlotGraph_mem pairing unions powers separation infinite),
    relationCompose_function_of_subset pairCode.2 depthSlotGraph_function (fun _ h => h)⟩

theorem externalOwnerLevels_entry_iff (hP0 : P0 ∈ M.sets) (x : ZFSet.{u}) (k : Nat) :
    ZFSet.pair x (natSetCode k) ∈ levels ↔ x ∈ F ∧
      ∃ v, ∃ n j : Nat, j < 3 ∧ ZFSet.pair x v ∈ owners ∧
        ZFSet.pair v (natSetCode n) ∈ depths ∧ ZFSet.pair x (natSetCode j) ∈ slots ∧
          k = depthSlotIndex n j := by
  change ZFSet.pair x (natSetCode k) ∈ relationCompose F (ZFSet.prod ZFSet.omega (natSetCode 3))
    ZFSet.omega pairs depthSlotGraph ↔ _
  rw [pair_mem_relationCompose]
  constructor
  · rintro ⟨hx, _, p, hp, pairEntry, rankEntry⟩
    obtain ⟨n, hn, j, hj, rfl⟩ := ZFSet.mem_prod.1 hp
    obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
    obtain ⟨j, bound, rfl⟩ := (mem_natSetCode j 3).1 hj
    have pairParts := (pair_mem_pairedGraph _ _ _ _ _ _ _ _).1 pairEntry
    obtain ⟨_, _, v, _, owned, depth⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 pairParts.2.2.2.1
    exact ⟨hx, v, n, j, bound, owned, depth, pairParts.2.2.2.2,
      ((pair_mem_depthSlotGraph n j k).1 rankEntry).2⟩
  · rintro ⟨hx, v, n, j, bound, owned, depth, slot, rfl⟩
    have owner := (data.externalStarOwner_ground_function group oldAction pairing unions powers separation infinite hG hP0).2
    have hv := (ZFSet.pair_mem_prod.1 (owner.1 owned)).2
    have hn := natSetCode_mem_omega n
    have hj := (natSetCode_mem_iff j 3).2 bound
    refine ⟨hx, natSetCode_mem_omega _, ZFSet.pair (natSetCode n) (natSetCode j),
      ZFSet.pair_mem_prod.2 ⟨hn, hj⟩, ?_, (pair_mem_depthSlotGraph n j _).2 ⟨bound, rfl⟩⟩
    apply (pair_mem_pairedGraph _ _ _ _ _ _ _ _).2
    refine ⟨hx, hn, hj, ?_, slot⟩
    exact (pair_mem_relationCompose _ _ _ _ _ _ _).2
      ⟨((mem_ownerFresh P B x).1 hx).1, hn, v, hv, owned, depth⟩

theorem externalOwnerLevels_monotone (hP0 : P0 ∈ M.sets) {x y : ZFSet.{u}} {k l : Nat}
    (lower : ZFSet.pair x y ∈ completion.externalPointOrder P0 r0 μ0 A0)
    (first : ZFSet.pair x (natSetCode k) ∈ levels)
    (second : ZFSet.pair y (natSetCode l) ∈ levels) : k ≤ l := by
  obtain ⟨_, v, n, j, hj, xv, vn, xj, rfl⟩ :=
    (data.externalOwnerLevels_entry_iff group oldAction pairing unions powers separation infinite hG hP0 x k).1 first
  obtain ⟨_, w, m, i, hi, yw, wm, yi, rfl⟩ :=
    (data.externalOwnerLevels_entry_iff group oldAction pairing unions powers separation infinite hG hP0 y l).1 second
  have depthOrder := data.externalStarOwner_order_depth group oldAction pairing unions powers separation infinite hG
    lower xv yw vn wm
  apply (depthSlotIndex_le_iff hj hi).2
  rcases Nat.lt_or_eq_of_le depthOrder.1 with less | same
  · exact Or.inl less
  · subst m
    have slotOrder := data.externalOwnerSlots_monotone group oldAction pairing unions powers separation infinite hG hP0
      lower xv yw vn wm xj yi
    refine Or.inr ⟨rfl, ?_⟩
    rcases slotOrder with equal | less
    · exact (natSetCode_injective equal).le
    · exact ((natSetCode_mem_iff j i).1 less).le

end GroundExternalGeometryInputs

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing.GroundExternalGeometryInputs
open SetFormula SetRealization
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets)
local notation "P" => completion.externalSeedCarrier P0 r0 μ0 A0
local notation "B" => completion.externalPointCarrier P0 r0 μ0 A0
local notation "F" => ownerFresh P B
local notation "letters" => externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)
local notation "requests" => externalRequestCarrier I P0 (externalRectangles P0 G r0 μ0 A0)
local notation "V" => M.externalStarVertices G letters requests m one
local notation "owners" => completion.externalStarOwner P0 r0 μ0 A0
local notation "depths" => M.externalStarDepth G letters requests m one
local notation "slots" => completion.externalOwnerSlots P0 r0 μ0 A0
local notation "levels" => completion.externalOwnerLevels P0 r0 μ0 A0
include data group oldAction pairing unions powers separation infinite hG

theorem externalOwnerLevels_rank (hP0 : P0 ∈ M.sets) {x v : ZFSet.{u}} {n j k : Nat}
    (owned : ZFSet.pair x v ∈ owners) (depth : ZFSet.pair v (natSetCode n) ∈ depths)
    (slot : ZFSet.pair x (natSetCode j) ∈ slots) (level : ZFSet.pair x (natSetCode k) ∈ levels) :
    j < 3 ∧ k = depthSlotIndex n j := by
  obtain ⟨_, v', n', j', bound, owned', depth', slot', equal⟩ :=
    (data.externalOwnerLevels_entry_iff group oldAction pairing unions powers separation infinite hG hP0 x k).1 level
  have ownerCode : FunctionGraphOn B owners :=
    ⟨_, (data.externalStarOwner_ground_function group oldAction pairing unions powers separation infinite hG hP0).2⟩
  have depthCode : FunctionGraphOn V depths :=
    ⟨_, (data.externalStarDepth_ground_function group oldAction pairing unions powers separation infinite hG).2⟩
  have slotCode : FunctionGraphOn F slots :=
    ⟨_, (data.externalOwnerSlots_ground_function group oldAction pairing unions powers separation infinite hG hP0).2⟩
  have hv := ownerCode.unique owned' owned
  subst v'
  have hn := natSetCode_injective (depthCode.unique depth' depth)
  have hj := natSetCode_injective (slotCode.unique slot' slot)
  subst n'
  subst j'
  exact ⟨bound, equal⟩

theorem externalOwnerLevels_equal_components (hP0 : P0 ∈ M.sets)
    {x y v w : ZFSet.{u}} {n m j i k : Nat}
    (firstOwner : ZFSet.pair x v ∈ owners) (secondOwner : ZFSet.pair y w ∈ owners)
    (firstDepth : ZFSet.pair v (natSetCode n) ∈ depths)
    (secondDepth : ZFSet.pair w (natSetCode m) ∈ depths)
    (firstSlot : ZFSet.pair x (natSetCode j) ∈ slots)
    (secondSlot : ZFSet.pair y (natSetCode i) ∈ slots)
    (first : ZFSet.pair x (natSetCode k) ∈ levels)
    (second : ZFSet.pair y (natSetCode k) ∈ levels) : n = m ∧ j = i := by
  have left := data.externalOwnerLevels_rank group oldAction pairing unions powers separation infinite hG hP0
    firstOwner firstDepth firstSlot first
  have right := data.externalOwnerLevels_rank group oldAction pairing unions powers separation infinite hG hP0
    secondOwner secondDepth secondSlot second
  exact (depthSlotIndex_eq_iff left.1 right.1).1 (left.2.symm.trans right.2)

theorem externalOwnerLevels_meet_lower (hP0 : P0 ∈ M.sets)
    {x y z v w : ZFSet.{u}} {k l : Nat}
    (firstOwner : ZFSet.pair x v ∈ owners) (secondOwner : ZFSet.pair y w ∈ owners)
    (different : v ≠ w) (first : ZFSet.pair x (natSetCode k) ∈ levels)
    (second : ZFSet.pair y (natSetCode k) ∈ levels)
    (meetEntry : ZFSet.pair (ZFSet.pair x y) z ∈ completion.externalPointMeet P0 r0 μ0 A0)
    (third : ZFSet.pair z (natSetCode l) ∈ levels) : l < k := by
  obtain ⟨_, v', n, j, hj, xv, vn, xj, eqK⟩ :=
    (data.externalOwnerLevels_entry_iff group oldAction pairing unions powers separation infinite hG hP0 x k).1 first
  obtain ⟨_, w', m, i, hi, yw, wm, yi, eqK'⟩ :=
    (data.externalOwnerLevels_entry_iff group oldAction pairing unions powers separation infinite hG hP0 y k).1 second
  obtain ⟨_, u, p, q, hq, zu, up, zq, eqL⟩ :=
    (data.externalOwnerLevels_entry_iff group oldAction pairing unions powers separation infinite hG hP0 z l).1 third
  have ownerCode : FunctionGraphOn B owners :=
    ⟨_, (data.externalStarOwner_ground_function group oldAction pairing unions powers separation infinite hG hP0).2⟩
  have hv := ownerCode.unique xv firstOwner
  have hw := ownerCode.unique yw secondOwner
  subst v'
  subst w'
  have same := ((depthSlotIndex_eq_iff hj hi).1 (eqK.symm.trans eqK')).1
  subst m
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP0
  have left := data.externalStarOwner_order_depth group oldAction pairing unions powers separation infinite hG
    (geometry.meet.lower_left x y z meetEntry) zu firstOwner up vn
  have right := data.externalStarOwner_order_depth group oldAction pairing unions powers separation infinite hG
    (geometry.meet.lower_right x y z meetEntry) zu secondOwner up wm
  have less : p < n := by
    apply Nat.lt_of_le_of_ne left.1
    intro equal
    exact different ((left.2 equal).symm.trans (right.2 equal))
  rw [eqL, eqK]
  exact (depthSlotIndex_lt_iff hq hj).2 (Or.inl less)

theorem externalOwnerLevels_meet_old_or_lower (hP0 : P0 ∈ M.sets)
    {x y z v w : ZFSet.{u}} {k : Nat}
    (firstOwner : ZFSet.pair x v ∈ owners) (secondOwner : ZFSet.pair y w ∈ owners)
    (different : v ≠ w) (first : ZFSet.pair x (natSetCode k) ∈ levels)
    (second : ZFSet.pair y (natSetCode k) ∈ levels)
    (meetEntry : ZFSet.pair (ZFSet.pair x y) z ∈ completion.externalPointMeet P0 r0 μ0 A0) :
    z ∈ P ∨ ∃ l < k, ZFSet.pair z (natSetCode l) ∈ levels := by
  by_cases old : z ∈ P
  · exact Or.inl old
  · have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP0
    have hz := (ZFSet.pair_mem_prod.1 (geometry.meet.order.relation (geometry.meet.lower_left x y z meetEntry))).1
    have code := (data.externalOwnerLevels_ground_function group oldAction pairing unions powers separation infinite hG hP0).2
    obtain ⟨l, entry, _⟩ := code.2 z ((mem_ownerFresh P B z).2 ⟨hz, old⟩)
    have hl := (ZFSet.pair_mem_prod.1 (code.1 entry)).2
    obtain ⟨l, rfl⟩ := (mem_omega_iff_natSetCode l).1 hl
    exact Or.inr ⟨l, data.externalOwnerLevels_meet_lower group oldAction pairing unions powers separation infinite hG hP0
      firstOwner secondOwner different first second meetEntry entry, entry⟩

end PartitionPilot.Forcing.GroundExternalGeometryInputs

namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

noncomputable def preparationFamilyImage (J N C E keyMap tupleMap k enums : ZFSet.{u}) : ZFSet.{u} :=
  relationCompose N J (ZFSet.prod C E) (relationConverse J N keyMap)
    (relationCompose J (ZFSet.prod C E) (ZFSet.prod C E) (pairedGraph J C E k enums) tupleMap)

noncomputable def preparationFamilyFirst (J N C E keyMap tupleMap k enums : ZFSet.{u}) : ZFSet.{u} :=
  relationCompose (relationImage J N keyMap) (ZFSet.prod C E) C (preparationFamilyImage J N C E keyMap tupleMap k enums)
    (productFirst C E)

noncomputable def preparationFamilySecond (J N C E keyMap tupleMap k enums : ZFSet.{u}) : ZFSet.{u} :=
  relationCompose (relationImage J N keyMap) (ZFSet.prod C E) E (preparationFamilyImage J N C E keyMap tupleMap k enums)
    (productSecond C E)

theorem preparationFamilyImage_function {J N C E keyMap tupleMap k enums : ZFSet.{u}}
    (keys : InjectionCode N N keyMap) (tuples : ZFSet.IsFunc (ZFSet.prod C E) (ZFSet.prod C E) tupleMap)
    (first : ZFSet.IsFunc J C k) (second : ZFSet.IsFunc J E enums) :
    ZFSet.IsFunc (relationImage J N keyMap) (ZFSet.prod C E)
      (preparationFamilyImage J N C E keyMap tupleMap k enums) := by
  have forward := relationCompose_function_of_subset
    (pairedGraph_function_of_subset first second (fun _ h => h)) tuples (fun _ h => h)
  let inverse := relationConverse J N keyMap
  let mapped := relationCompose J (ZFSet.prod C E) (ZFSet.prod C E) (pairedGraph J C E k enums) tupleMap
  have uniqueInverse : ∀ x v w, ZFSet.pair x v ∈ inverse → ZFSet.pair x w ∈ inverse → v = w := by
    intro x v w hv hw
    exact keys.injective v w x ((pair_mem_relationConverse J N keyMap v x).1 hv).2.2
      ((pair_mem_relationConverse J N keyMap w x).1 hw).2.2
  refine ⟨?_, ?_⟩
  · intro z hz
    obtain ⟨x, hx, v, hv, y, hy, rfl, xv, _⟩ := (mem_relationCompose N J (ZFSet.prod C E) inverse mapped z).1 hz
    exact ZFSet.pair_mem_prod.2 ⟨(mem_relationImage J N keyMap x).2
      ⟨hx, v, hv, ((pair_mem_relationConverse J N keyMap v x).1 xv).2.2⟩, hy⟩
  · intro x hx
    obtain ⟨hxN, v, hv, vx⟩ := (mem_relationImage J N keyMap x).1 hx
    have xv := (pair_mem_relationConverse J N keyMap v x).2 ⟨hv, hxN, vx⟩
    obtain ⟨y, vy, unique⟩ := forward.2 v hv
    have hy := (ZFSet.pair_mem_prod.1 (forward.1 vy)).2
    refine ⟨y, (pair_mem_relationCompose N J (ZFSet.prod C E) inverse mapped x y).2
      ⟨hxN, hy, v, hv, xv, vy⟩, ?_⟩
    intro other entry
    obtain ⟨_, _, w, _, xw, wy⟩ := (pair_mem_relationCompose N J (ZFSet.prod C E) inverse mapped x other).1 entry
    exact unique other (uniqueInverse x w v xw xv ▸ wy)

theorem preparationFamilyImages_function {J N C E keyMap tupleMap k enums : ZFSet.{u}}
    (keys : InjectionCode N N keyMap) (tuples : ZFSet.IsFunc (ZFSet.prod C E) (ZFSet.prod C E) tupleMap)
    (first : ZFSet.IsFunc J C k) (second : ZFSet.IsFunc J E enums) :
    ZFSet.IsFunc (relationImage J N keyMap) C (preparationFamilyFirst J N C E keyMap tupleMap k enums) ∧
    ZFSet.IsFunc (relationImage J N keyMap) E (preparationFamilySecond J N C E keyMap tupleMap k enums) := by
  have joint := preparationFamilyImage_function keys tuples first second
  exact ⟨relationCompose_function_of_subset joint (productFirst_function C E) (fun _ h => h),
    relationCompose_function_of_subset joint (productSecond_function C E) (fun _ h => h)⟩

theorem preparationFamilyImages_entry {J N C E keyMap tupleMap k enums : ZFSet.{u}}
    (keys : InjectionCode N N keyMap) (tuples : ZFSet.IsFunc (ZFSet.prod C E) (ZFSet.prod C E) tupleMap)
    (first : ZFSet.IsFunc J C k) (second : ZFSet.IsFunc J E enums) (x c e : ZFSet.{u}) :
    (ZFSet.pair x c ∈ preparationFamilyFirst J N C E keyMap tupleMap k enums ∧
      ZFSet.pair x e ∈ preparationFamilySecond J N C E keyMap tupleMap k enums) ↔
    ∃ z a b, ZFSet.pair z a ∈ k ∧ ZFSet.pair z b ∈ enums ∧ ZFSet.pair z x ∈ keyMap ∧
      ZFSet.pair (ZFSet.pair a b) (ZFSet.pair c e) ∈ tupleMap := by
  let joint := preparationFamilyImage J N C E keyMap tupleMap k enums
  have jointFunction := preparationFamilyImage_function keys tuples first second
  have paired (x c e : ZFSet.{u}) :
      (ZFSet.pair x c ∈ preparationFamilyFirst J N C E keyMap tupleMap k enums ∧
        ZFSet.pair x e ∈ preparationFamilySecond J N C E keyMap tupleMap k enums) ↔
      ZFSet.pair x (ZFSet.pair c e) ∈ joint := by
    constructor
    · rintro ⟨hc, he⟩
      obtain ⟨_, _, y, _, xy, yc⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 hc
      obtain ⟨_, _, y', _, xy', ye⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 he
      obtain ⟨a, ha, b, hb, eqc⟩ := (mem_productFirst C E _).1 yc
      obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eqc
      obtain ⟨a', _, b', _, eqe⟩ := (mem_productSecond C E _).1 ye
      obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eqe
      obtain ⟨_, _, unique⟩ := jointFunction.2 x (ZFSet.pair_mem_prod.1 (jointFunction.1 xy)).1
      have same := (unique _ xy).trans (unique _ xy').symm
      obtain ⟨_, sameB⟩ := ZFSet.pair_inj.1 same
      exact sameB ▸ xy
    · intro entry
      have bounds := ZFSet.pair_mem_prod.1 (jointFunction.1 entry)
      have out := ZFSet.pair_mem_prod.1 bounds.2
      exact ⟨(pair_mem_relationCompose _ _ _ _ _ _ _).2
        ⟨bounds.1, out.1, ZFSet.pair c e, bounds.2, entry, (mem_productFirst C E _).2 ⟨c, out.1, e, out.2, rfl⟩⟩,
        (pair_mem_relationCompose _ _ _ _ _ _ _).2
        ⟨bounds.1, out.2, ZFSet.pair c e, bounds.2, entry, (mem_productSecond C E _).2 ⟨c, out.1, e, out.2, rfl⟩⟩⟩
  rw [paired]
  constructor
  · intro entry
    obtain ⟨_, _, z, _, inverse, forward⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 entry
    obtain ⟨_, _, value, _, old, moved⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 forward
    obtain ⟨z', _, a, _, b, _, eq, ka, eb⟩ := (mem_pairedGraph J C E k enums _).1 old
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact ⟨z, a, b, ka, eb, ((pair_mem_relationConverse J N keyMap z x).1 inverse).2.2, moved⟩
  · rintro ⟨z, a, b, ka, eb, key, moved⟩
    have kaBounds := ZFSet.pair_mem_prod.1 (first.1 ka)
    have ebBounds := ZFSet.pair_mem_prod.1 (second.1 eb)
    have hx := (ZFSet.pair_mem_prod.1 (keys.function.1 key)).2
    have out := (ZFSet.pair_mem_prod.1 (tuples.1 moved)).2
    have ab := ZFSet.pair_mem_prod.2 ⟨kaBounds.2, ebBounds.2⟩
    exact (pair_mem_relationCompose _ _ _ _ _ _ _).2
      ⟨hx, out, z, kaBounds.1, (pair_mem_relationConverse J N keyMap z x).2 ⟨kaBounds.1, hx, key⟩,
        (pair_mem_relationCompose _ _ _ _ _ _ _).2 ⟨kaBounds.1, out, ZFSet.pair a b, ab,
          (pair_mem_pairedGraph J C E k enums z a b).2 ⟨kaBounds.1, kaBounds.2, ebBounds.2, ka, eb⟩, moved⟩⟩

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem preparationFamilyImages_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {J N C E keyMap tupleMap k enums : ZFSet.{u}}
    (hJ : J ∈ M.sets) (hN : N ∈ M.sets) (hC : C ∈ M.sets) (hE : E ∈ M.sets)
    (hKeys : keyMap ∈ M.sets) (hTuples : tupleMap ∈ M.sets) (hk : k ∈ M.sets) (he : enums ∈ M.sets) :
    preparationFamilyImage J N C E keyMap tupleMap k enums ∈ M.sets ∧
      preparationFamilyFirst J N C E keyMap tupleMap k enums ∈ M.sets ∧
      preparationFamilySecond J N C E keyMap tupleMap k enums ∈ M.sets := by
  have hCE := M.prod_mem pairing unions powers separation hC hE
  have joint := M.relationCompose_mem pairing unions powers separation hN hJ hCE
    (M.relationConverse_mem pairing unions powers separation hJ hN hKeys)
    (M.relationCompose_mem pairing unions powers separation hJ hCE hCE
      (M.pairedGraph_mem pairing unions powers separation hJ hC hE hk he) hTuples)
  have hImage := M.relationImage_mem separation hJ hN hKeys
  exact ⟨joint, M.relationCompose_mem pairing unions powers separation hImage hCE hC joint
    (M.productFirst_mem pairing unions powers separation hC hE),
    M.relationCompose_mem pairing unions powers separation hImage hCE hE joint
      (M.productSecond_mem pairing unions powers separation hC hE)⟩

end TransitiveGround

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing.GroundExternalGeometryInputs
open SetFormula SetRealization Compression.RecursiveMaps.CosetGeometry
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets)
local notation "P" => completion.externalSeedCarrier P0 r0 μ0 A0
local notation "B" => completion.externalPointCarrier P0 r0 μ0 A0
local notation "F" => ownerFresh P B
local notation "letters" => externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)
local notation "requests" => externalRequestCarrier I P0 (externalRectangles P0 G r0 μ0 A0)
local notation "V" => M.externalStarVertices G letters requests m one
local notation "owners" => completion.externalStarOwner P0 r0 μ0 A0
local notation "depths" => M.externalStarDepth G letters requests m one
local notation "supports" => completion.externalStarSupports P0 r0 μ0 A0
local notation "slots" => completion.externalOwnerSlots P0 r0 μ0 A0
local notation "slotPoints" => completion.externalTileSlotPoints P0 r0 μ0 A0
local notation "levels" => completion.externalOwnerLevels P0 r0 μ0 A0
local notation "family" => completion.externalFamily group oldAction data.original
local notation "action" => completion.algebra.union.action.toOrderAction group completion.algebra.union.meet
local notation "vpres" => data.externalStarVertexPresentation group oldAction pairing unions powers separation infinite hG
local notation "q" => data.externalPointPresentation group oldAction pairing unions powers separation infinite hG
include data group oldAction pairing unions powers separation infinite hG

theorem externalTileSlotPoints_support {v j x : ZFSet.{u}}
    (supported : ZFSet.pair (ZFSet.pair v j) x ∈ slotPoints) : ZFSet.pair v x ∈ supports := by
  let := group.toGroup
  obtain ⟨w, r, i, a, rfl, rfl, rfl⟩ :=
    data.externalTileSlotPoints_decode group oldAction pairing unions powers separation infinite hG supported
  apply (data.externalStarSupports_iff group oldAction pairing unions powers separation infinite hG _ _).2
  exact ⟨((family).flatVertex r i).toFun a, rfl⟩

theorem externalOwnerSlots_supported (hP0 : P0 ∈ M.sets) {x v j : ZFSet.{u}}
    (owned : ZFSet.pair x v ∈ owners) (slot : ZFSet.pair x j ∈ slots) :
    ZFSet.pair (ZFSet.pair v j) x ∈ slotPoints := by
  have function := (data.externalStarOwner_ground_function group oldAction pairing unions powers separation infinite hG hP0).2
  exact ((pair_mem_leastSlotOwnerGraph_of_owner function owned).1 slot).2.2.1

theorem externalOwnerLevels_slot_support (hP0 : P0 ∈ M.sets) {x : ZFSet.{u}} {k : Nat}
    (level : ZFSet.pair x (natSetCode k) ∈ levels) : x ∈ F ∧
      ∃ v, ∃ n j : Nat, j < 3 ∧ ZFSet.pair x v ∈ owners ∧
        ZFSet.pair v (natSetCode n) ∈ depths ∧ ZFSet.pair x (natSetCode j) ∈ slots ∧
          ZFSet.pair (ZFSet.pair v (natSetCode j)) x ∈ slotPoints ∧ k = depthSlotIndex n j := by
  obtain ⟨hx, v, n, j, bound, owned, depth, slot, equal⟩ :=
    (data.externalOwnerLevels_entry_iff group oldAction pairing unions powers separation infinite hG hP0 x k).1 level
  exact ⟨hx, v, n, j, bound, owned, depth, slot,
    data.externalOwnerSlots_supported group oldAction pairing unions powers separation infinite hG hP0 owned slot, equal⟩

theorem externalOwnerLevels_slot_bound (hP0 : P0 ∈ M.sets) {v x : ZFSet.{u}} {n j k : Nat}
    (supported : ZFSet.pair (ZFSet.pair v (natSetCode j)) x ∈ slotPoints)
    (depth : ZFSet.pair v (natSetCode n) ∈ depths)
    (level : ZFSet.pair x (natSetCode k) ∈ levels) : k ≤ depthSlotIndex n j := by
  obtain ⟨hx, u, d, i, hi, owned, ownerDepth, slot, equal⟩ :=
    (data.externalOwnerLevels_entry_iff group oldAction pairing unions powers separation infinite hG hP0 x k).1 level
  have support := data.externalTileSlotPoints_support group oldAction pairing unions powers separation infinite hG supported
  have shape := (pair_mem_externalTileSlotSupports _ _ _ _ _ _ _ _ _ _).1 supported
  have hj := shape.2.1
  have ownerFunction := (data.externalStarOwner_ground_function group oldAction pairing unions powers separation infinite hG hP0).2
  have depthCode : FunctionGraphOn V depths :=
    ⟨_, (data.externalStarDepth_ground_function group oldAction pairing unions powers separation infinite hG).2⟩
  have least := (pair_mem_leastSupportGraph _ _ _ _ _ _).1 owned
  obtain ⟨a, _, ua, minimal⟩ := least.2.2.2
  have eqA := depthCode.unique ua ownerDepth
  subst a
  have before : d ≤ n := Nat.le_of_not_gt (fun less => minimal v shape.1 (natSetCode n)
    (natSetCode_mem_omega n) support depth ((natSetCode_mem_iff n d).2 less))
  rw [equal]
  apply (depthSlotIndex_le_iff hi ((natSetCode_mem_iff j 3).1 hj)).2
  rcases Nat.lt_or_eq_of_le before with less | same
  · exact Or.inl less
  · subst d
    have tileOwned : ZFSet.pair x v ∈ owners :=
      (pair_mem_leastSupportGraph _ _ _ _ _ _).2
        ⟨((mem_ownerFresh P B x).1 hx).1, shape.1, support,
          natSetCode n, natSetCode_mem_omega n, depth, minimal⟩
    have leastSlot := ((pair_mem_leastSlotOwnerGraph_of_owner ownerFunction tileOwned).1 slot).2.2
    have slotOrder := leastSlot.le ((natSetCode_mem_iff i 3).2 hi) hj supported
    refine Or.inr ⟨rfl, ?_⟩
    rcases slotOrder with same | less
    · exact (natSetCode_injective same).le
    · exact ((natSetCode_mem_iff i j).1 less).le

theorem externalSlotCopy_old_or_level_bound (hP0 : P0 ∈ M.sets)
    {v x : ZFSet.{u}} {n j : Nat}
    (supported : ZFSet.pair (ZFSet.pair v (natSetCode j)) x ∈ slotPoints)
    (depth : ZFSet.pair v (natSetCode n) ∈ depths) :
    x ∈ P ∨ ∃ k ≤ depthSlotIndex n j, ZFSet.pair x (natSetCode k) ∈ levels := by
  by_cases old : x ∈ P
  · exact Or.inl old
  · have shape := (pair_mem_externalTileSlotSupports _ _ _ _ _ _ _ _ _ _).1 supported
    have function := (data.externalOwnerLevels_ground_function group oldAction pairing unions powers separation infinite hG hP0).2
    obtain ⟨k, level, _⟩ := function.2 x ((mem_ownerFresh P B x).2 ⟨shape.2.2.1, old⟩)
    have hk := (ZFSet.pair_mem_prod.1 (function.1 level)).2
    obtain ⟨k, rfl⟩ := (mem_omega_iff_natSetCode k).1 hk
    exact Or.inr ⟨k, data.externalOwnerLevels_slot_bound group oldAction pairing unions powers separation infinite hG hP0
      supported depth level, level⟩

end PartitionPilot.Forcing.GroundExternalGeometryInputs

end OAI
