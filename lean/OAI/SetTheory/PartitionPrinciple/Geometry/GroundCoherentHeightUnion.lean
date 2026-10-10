import OAI.SetTheory.PartitionPrinciple.Geometry.GroundCompressionStampBounds
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundMainStageFromCodes

namespace OAI

section

namespace PartitionPilot.Forcing.NatUnionCode
universe u

theorem strictLexHeight {P r h : Nat → ZFSet.{u}} {U R H C D rD : ZFSet.{u}}
    (carrier : NatUnionCode P U) (relation : NatUnionCode r R) (height : NatUnionCode h H)
    (orders : ∀ n, PartialOrderCode (P n) (r n))
    (codes : ∀ n, StrictLexHeightCode (P n) C D (r n) (h n) rD)
    (heightMono : ∀ n m, n ≤ m → h n ⊆ h m) : StrictLexHeightCode U C D R H rD := by
  have function := carrier.isFunc (NatUnionCode.constant (ZFSet.prod C D)) height
    (fun n => (codes n).function) heightMono
  refine ⟨function, ?_⟩
  intro x _ y _ c q d v lower different first second
  obtain ⟨n, finiteLower⟩ := (relation (ZFSet.pair x y)).1 lower
  have bounds := ZFSet.pair_mem_prod.1 ((orders n).relation finiteLower)
  exact (codes n).strict x bounds.1 y bounds.2 c q d v finiteLower different
    ((height.function_entry_iff function (fun n => (codes n).function) n bounds.1).1 first)
    ((height.function_entry_iff function (fun n => (codes n).function) n bounds.2).1 second)

theorem height_entry_iff {P r h : Nat → ZFSet.{u}} {U R H C D rD : ZFSet.{u}}
    (height : NatUnionCode h H) (code : StrictLexHeightCode U C D R H rD)
    (codes : ∀ n, StrictLexHeightCode (P n) C D (r n) (h n) rD)
    (n : Nat) {x y : ZFSet.{u}} (hx : x ∈ P n) :
    ZFSet.pair x y ∈ H ↔ ZFSet.pair x y ∈ h n :=
  height.function_entry_iff code.function (fun n => (codes n).function) n hx

theorem height_column_bound {h : Nat → ZFSet.{u}} {H B : ZFSet.{u}}
    (height : NatUnionCode h H)
    (bounded : ∀ n x c q, ZFSet.pair x (ZFSet.pair c q) ∈ h n → c ∈ B) :
    ∀ x c q, ZFSet.pair x (ZFSet.pair c q) ∈ H → c ∈ B := by
  intro x c q entry
  obtain ⟨n, finiteEntry⟩ := (height (ZFSet.pair x (ZFSet.pair c q))).1 entry
  exact bounded n x c q finiteEntry

theorem height_weak_bound {h : Nat → ZFSet.{u}} {H bound order : ZFSet.{u}}
    (height : NatUnionCode h H)
    (bounded : ∀ n x y, ZFSet.pair x y ∈ h n →
      y = bound ∨ ZFSet.pair y bound ∈ order) :
    ∀ x y, ZFSet.pair x y ∈ H → y = bound ∨ ZFSet.pair y bound ∈ order := by
  intro x y entry
  obtain ⟨n, finiteEntry⟩ := (height (ZFSet.pair x y)).1 entry
  exact bounded n x y finiteEntry

end PartitionPilot.Forcing.NatUnionCode



namespace PartitionPilot.Forcing
universe u

theorem natGraphMono_of_adjacent {graphs : Nat → ZFSet.{u}}
    (adjacent : ∀ n, graphs n ⊆ graphs (n + 1)) :
    ∀ n m, n ≤ m → graphs n ⊆ graphs m := by
  intro n m before
  induction m, before using Nat.le_induction with
  | base => exact fun _ hx => hx
  | succ m _ ih => exact fun _ hx => adjacent m (ih hx)

namespace TransitiveGround
open SetFormula

theorem exists_groundCoherentHeightUnion (M : TransitiveGround.{u})
    (unions : Realize M.sets SetFormula.union Fin.elim0) (separation : SeparationSchema M.sets)
    (hω : (ZFSet.omega : ZFSet.{u}) ∈ M.sets)
    {family U R C D rD B : ZFSet.{u}} {P r : Nat → ZFSet.{u}}
    (hFamily : family ∈ M.sets) (function : FunctionGraphOn ZFSet.omega family)
    (carrier : NatUnionCode P U) (relation : NatUnionCode r R)
    (orders : ∀ n, PartialOrderCode (P n) (r n))
    (codes : ∀ n, StrictLexHeightCode (P n) C D (r n) (function.natValue n) rD)
    (adjacent : ∀ n, function.natValue n ⊆ function.natValue (n + 1))
    (columns : ∀ n x c q, ZFSet.pair x (ZFSet.pair c q) ∈ function.natValue n → c ∈ B) :
    ∃ height ∈ M.sets,
      NatUnionCode function.natValue height ∧ StrictLexHeightCode U C D R height rD ∧
      (∀ n x, x ∈ P n → ∀ y, ZFSet.pair x y ∈ height ↔
        ZFSet.pair x y ∈ function.natValue n) ∧
      ∀ x c q, ZFSet.pair x (ZFSet.pair c q) ∈ height → c ∈ B := by
  have exactUnion := naturalFamilyUnion_code function
  have code := carrier.strictLexHeight relation exactUnion orders codes (natGraphMono_of_adjacent adjacent)
  exact ⟨naturalFamilyUnion family, M.naturalFamilyUnion_mem unions separation hω hFamily,
    exactUnion, code,
    fun n x hx _ => exactUnion.height_entry_iff code codes n hx,
    exactUnion.height_column_bound columns⟩

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
