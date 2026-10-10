import OAI.SetTheory.PartitionPrinciple.Models.GroundCountableQuotients

namespace OAI


namespace PartitionPilot.Forcing

open Compression.RecursiveMaps
universe u

structure StrictLinearOrderCode (D r : ZFSet.{u}) : Prop where
  shape : r ⊆ ZFSet.prod D D
  irrefl : ∀ x ∈ D, ZFSet.pair x x ∉ r
  trans : ∀ x y z, ZFSet.pair x y ∈ r → ZFSet.pair y z ∈ r → ZFSet.pair x z ∈ r
  compare : ∀ x ∈ D, ∀ y ∈ D, ZFSet.pair x y ∈ r ∨ x = y ∨ ZFSet.pair y x ∈ r

structure DenseOrderCode (D r : ZFSet.{u}) : Prop extends StrictLinearOrderCode D r where
  between : ∀ x y, ZFSet.pair x y ∈ r → ∃ z ∈ D, ZFSet.pair x z ∈ r ∧ ZFSet.pair z y ∈ r

def StrictLinearOrderCode.toLinearHeightOrder {D r : ZFSet.{u}} (code : StrictLinearOrderCode D r) :
    LinearHeightOrder {x : ZFSet.{u} // x ∈ D} where
  lt x y := ZFSet.pair x.val y.val ∈ r
  irrefl x := code.irrefl x.val x.property
  trans {x y z} := code.trans x.val y.val z.val
  compare x y := (code.compare x.val x.property y.val y.property).imp id
    (fun h => h.imp (fun equal => Subtype.ext equal) id)

def DenseOrderCode.toDenseHeightOrder {D r : ZFSet.{u}} (code : DenseOrderCode D r) :
    DenseHeightOrder {x : ZFSet.{u} // x ∈ D} where
  toLinearHeightOrder := code.toStrictLinearOrderCode.toLinearHeightOrder
  between x y lower := by
    obtain ⟨z, hz, left, right⟩ := code.between x.val y.val lower
    exact ⟨⟨z, hz⟩, left, right⟩

def intervalCandidate (D r lower upper lo hi x : ZFSet.{u}) : Prop :=
  x ∈ D ∧ ZFSet.pair lo x ∈ r ∧ ZFSet.pair x hi ∈ r ∧
    (∀ y ∈ lower, ZFSet.pair y x ∈ r) ∧ (∀ y ∈ upper, ZFSet.pair x y ∈ r)

theorem DenseOrderCode.finite_interval_candidate {D r lower upper lo hi : ZFSet.{u}}
    (code : DenseOrderCode D r) (loD : lo ∈ D) (hiD : hi ∈ D)
    (lowerD : lower ⊆ D) (upperD : upper ⊆ D)
    (finiteLower : lower.toSet.Finite) (finiteUpper : upper.toSet.Finite)
    (gap : ZFSet.pair lo hi ∈ r)
    (lowerHi : ∀ x ∈ lower, ZFSet.pair x hi ∈ r)
    (loUpper : ∀ y ∈ upper, ZFSet.pair lo y ∈ r)
    (separated : ∀ x ∈ lower, ∀ y ∈ upper, ZFSet.pair x y ∈ r) :
    ∃ x, intervalCandidate D r lower upper lo hi x := by
  classical
  have lowerFinite : (Subtype.val ⁻¹' lower.toSet : Set {x : ZFSet.{u} // x ∈ D}).Finite :=
    Set.Finite.preimage (fun _ _ _ _ equal => Subtype.ext equal) finiteLower
  have upperFinite : (Subtype.val ⁻¹' upper.toSet : Set {x : ZFSet.{u} // x ∈ D}).Finite :=
    Set.Finite.preimage (fun _ _ _ _ equal => Subtype.ext equal) finiteUpper
  let lowers := lowerFinite.toFinset.toList
  let uppers := upperFinite.toFinset.toList
  have lowerSpec (x : {x : ZFSet.{u} // x ∈ D}) : x ∈ lowers ↔ x.val ∈ lower := by
    simp only [lowers, Finset.mem_toList, Set.Finite.mem_toFinset, Set.mem_preimage]
    rfl
  have upperSpec (x : {x : ZFSet.{u} // x ∈ D}) : x ∈ uppers ↔ x.val ∈ upper := by
    simp only [uppers, Finset.mem_toList, Set.Finite.mem_toFinset, Set.mem_preimage]
    rfl
  obtain ⟨x, left, right, aboveLower, belowUpper⟩ := code.toDenseHeightOrder.finite_gap
    ⟨lo, loD⟩ ⟨hi, hiD⟩ lowers uppers gap
    (fun x hx => lowerHi x.val ((lowerSpec x).1 hx))
    (fun y hy => loUpper y.val ((upperSpec y).1 hy))
    (fun x hx y hy => separated x.val ((lowerSpec x).1 hx) y.val ((upperSpec y).1 hy))
  exact ⟨x.val, x.property, left, right,
    fun y hy => aboveLower ⟨y, lowerD hy⟩ ((lowerSpec _).2 hy),
    fun y hy => belowUpper ⟨y, upperD hy⟩ ((upperSpec _).2 hy)⟩

end PartitionPilot.Forcing

end OAI
