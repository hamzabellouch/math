import OAI.RingTheory.DirectFiniteness.DiagramReduction

namespace OAI

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.GluedGroup
variable {V F : Type} (Inc : F → Finset V) (ℓ : ℕ)
variable (incMap : ∀ v : V, {f : F // v ∈ Inc f} → (ZMod ℓ →+ (Fin 2 → ZMod ℓ)))

def totalMap (v : V) (f : F) : ZMod ℓ →+ (Fin 2 → ZMod ℓ) :=
  if h : v ∈ Inc f then incMap v ⟨f, h⟩ else 0

@[simp] lemma totalMap_of_mem (v : V) (f : F) (h : v ∈ Inc f) :
    totalMap Inc ℓ incMap v f = incMap v ⟨f, h⟩ := dite_eq_left h

def signedToken (s : Generator (F := F) ℓ × Bool) : F × ZMod ℓ :=
  (s.1.1, if s.2 then s.1.2.val else -s.1.2.val)

def Allowed (w : List (Generator (F := F) ℓ × Bool)) : Prop :=
  ∃ v : V, (∀ t ∈ w.map (signedToken ℓ), v ∈ Inc t.1) ∧
    ((w.map (signedToken ℓ)).map (fun t => totalMap Inc ℓ incMap v t.1 t.2)).sum = 0

lemma signedToken_inv (s : Generator (F := F) ℓ × Bool) :
    signedToken ℓ (s.1, !s.2) = ((signedToken ℓ s).1, -(signedToken ℓ s).2) := by
  rcases s with ⟨s, b⟩
  cases b <;> simp [signedToken]

lemma allowed_inv (w : List (Generator (F := F) ℓ × Bool))
    (h : Allowed Inc ℓ incMap w) : Allowed Inc ℓ incMap (FreeGroup.invRev w) := by
  obtain ⟨v, hi, hs⟩ := h
  refine ⟨v, ?_, ?_⟩
  · intro t ht
    simp only [FreeGroup.invRev, List.map_reverse, List.map_map, List.mem_reverse,
      List.mem_map] at ht
    obtain ⟨s, hs', rfl⟩ := ht
    change v ∈ Inc (signedToken ℓ (s.1, !s.2)).1
    rw [signedToken_inv]
    exact hi (signedToken ℓ s) (List.mem_map_of_mem hs')
  · let weight := fun token : Generator (F := F) ℓ × Bool =>
      totalMap Inc ℓ incMap v (signedToken ℓ token).1 (signedToken ℓ token).2
    have inverse_weight (token : Generator (F := F) ℓ × Bool) :
        weight (token.1, !token.2) = -weight token := by
      dsimp only [weight]
      rw [signedToken_inv]
      exact map_neg _ _
    have weights : (FreeGroup.invRev w).map weight =
        ((w.map weight).map Neg.neg).reverse := by
      rw [FreeGroup.invRev, List.map_reverse, List.map_map, List.map_map]
      exact congrArg List.reverse (List.map_congr_left fun token _ => inverse_weight token)
    have total : (w.map weight).sum = 0 := by
      rw [List.map_map] at hs
      exact hs
    rw [List.map_map]
    change ((FreeGroup.invRev w).map weight).sum = 0
    rw [weights, List.sum_reverse, ← List.sum_neg, total, neg_zero]

lemma allowed_cancel (hInc : ∀ f, (Inc f).Nonempty)
    (g : Generator (F := F) ℓ) (b : Bool) :
    Allowed Inc ℓ incMap [(g, b), (g, !b)] := by
  obtain ⟨v, hv⟩ := hInc g.1
  refine ⟨v, ?_, ?_⟩
  · intro t ht
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;> exact hv
  · cases b <;> simp [signedToken]

end KaplanskyCounterexample.GluedGroup

end

end OAI
