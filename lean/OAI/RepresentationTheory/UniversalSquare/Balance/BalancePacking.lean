import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Balance.BalanceLeaves
import OAI.RepresentationTheory.UniversalSquare.Balance.BalanceLift

namespace OAI

/-! Balance Packing. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl.Balance

structure Packing {n d e : ℕ} (v : WordSpace n d)
    (A : Fin (d*d) → Prop) (label : Fin (d*d) → ℕ) (w : WordSpace n e) where
  G : Type
  [groupG : Group G]
  [finiteG : Finite G]
  Y : Type
  [addY : AddCommGroup Y]
  [moduleY : Module ℂ Y]
  [finiteY : FiniteDimensional ℂ Y]
  c : Fin n → ℕ
  σ : ℕ → ℤ
  φ : G →* fiberGroup c
  τ : Representation ℂ G Y
  piece : Piece v c A label σ φ τ
  support : SupportLE (cyclic (wordRep n e) w).toRepresentation
    (Representation.coind ((fiberGroup c).subtype.comp φ) τ)

attribute [instance] Packing.groupG Packing.finiteG Packing.addY Packing.moduleY Packing.finiteY

def Packing.join {n a b d E : ℕ} {v : WordSpace a d} {u : WordSpace b d}
    {A : Fin (d*d) → Prop} {label : Fin (d*d) → ℕ}
    {w : WordSpace a E} {z : WordSpace b E}
    (P : Packing v A label w) (Q : Packing u A label z)
    (e : Fin n ≃ Fin a ⊕ Fin b) (hd : ∀ i j, P.c i ≠ Q.c j) :
    Packing (positionProduct e v u) A label (positionProduct e w z) := by
  letI : AddCommGroup (P.Y ⊗[ℂ] Q.Y) := Module.addCommMonoidToAddCommGroup ℂ
  exact {
    G := P.G × Q.G
    Y := P.Y ⊗[ℂ] Q.Y
    c := joinedLabels e P.c Q.c
    σ := P.σ + Q.σ
    φ := (joinedFiberHom e P.c Q.c).comp (P.φ.prodMap Q.φ)
    τ := outer P.τ Q.τ
    piece := P.piece.join Q.piece e hd
    support := product_supportLE_coind
      ((fiberGroup P.c).subtype.comp P.φ) ((fiberGroup Q.c).subtype.comp Q.φ)
      P.τ Q.τ e w z P.support Q.support }

def Packing.map {n d e E : ℕ} {v : WordSpace n d}
    {A : Fin (d*d) → Prop} {label : Fin (d*d) → ℕ} {w : WordSpace n e}
    (P : Packing v A label w)
    (T : Representation.IntertwiningMap (wordRep n e) (wordRep n E)) :
    Packing v A label (T w) :=
  { P with support := P.support.cyclic_image w T }

def Packing.lift {n d D e : ℕ} {v : WordSpace n d} {w : WordSpace n e}
    (f : Fin d → Fin D) (hf : ∀ a, (f a).val = a.val)
    (A : Fin (D*D) → Prop) (label : Fin (D*D) → ℕ)
    (P : Packing v (A ∘ pairLetterMap f f) (label ∘ pairLetterMap f f) w) :
    Packing (letterLift f v) A label w :=
  { P with piece := P.piece.lift f hf A label }

def Packing.replace {n d e E : ℕ} {v : WordSpace n d}
    {A : Fin (d*d) → Prop} {label : Fin (d*d) → ℕ}
    {w : WordSpace n e} (P : Packing v A label w) (z : WordSpace n E)
    (h : SupportLE (cyclic (wordRep n E) z).toRepresentation
      (cyclic (wordRep n e) w).toRepresentation) : Packing v A label z :=
  { P with support := h.trans P.support }

def boundedPacking {n e : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (k : ℕ) (I : Set ℕ)
    (A : Fin (μ.colLen 0 * μ.colLen 0) → Prop)
    (label : Fin (μ.colLen 0 * μ.colLen 0) → ℕ)
    (h : ∀ a, (A a ∧ label a = k) ↔ output a ∈ I)
    (hs : SupportLE (wordRep n e)
      (projectedSpechtTensor t t (inOutputs I) (inOutputs_invariant I)).toRepresentation)
    (w : WordSpace n e) : Packing (polytabloid t) A label w := by
  let W := projectedSpechtTensor t t (inOutputs I) (inOutputs_invariant I)
  let φ := (fiberGroup (fun _ : Fin n => k)).subtype.comp (singleFiberHom n k)
  have hi : Function.Injective (coindLift (ρ := W.toRepresentation) φ (Representation.IntertwiningMap.id W.toRepresentation)) := by
    intro x y hxy
    have he := congrArg (fun z : Representation.coindV φ W.toRepresentation => z.val 1) hxy
    change W.toRepresentation 1 x = W.toRepresentation 1 y at he
    simpa only [map_one,Module.End.one_apply] using he
  refine {
    G := Equiv.Perm (Fin n)
    Y := W.toSubmodule
    c := fun _ => k
    σ := columnOutputSums t (fun _ => k)
    φ := singleFiberHom n k
    τ := W.toRepresentation
    piece := projectedPiece t k I A label h
    support := ?_ }
  exact ((SupportLE.of_injective (subrepInclusion (cyclic (wordRep n e) w))
    Subtype.val_injective).trans hs).trans (SupportLE.of_injective _ hi)

theorem Packing.kronecker_pos {n : ℕ} {lam μ θ : YoungDiagram}
    (a : Tableau n lam) (t : Tableau n μ)
    {A : Fin (lam.colLen 0 * lam.colLen 0) → Prop}
    {label : Fin (lam.colLen 0 * lam.colLen 0) → ℕ}
    (w : Fin n → Fin (θ.colLen 0))
    (P : Packing (polytabloid a) A label (Pi.single w 1))
    (ho : ∀ x y, A x → A y → label x < label y → output x < output y)
    (hc : μ.card = θ.card) (hd : Dominates μ θ)
    (e : Equiv.Perm (Fin (θ.colLen 0)))
    (hw : ∀ j, (Finset.univ.filter (fun i => w i = e j)).card = θ.rowLen j) :
    0 < kronecker a a t :=
  P.piece.kronecker_pos a t ho θ hc hd w e hw P.support

end Saxl.Balance
end
end

end OAI
