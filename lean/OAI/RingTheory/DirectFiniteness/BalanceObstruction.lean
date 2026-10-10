import OAI.RingTheory.DirectFiniteness.PlanarDiagrams

namespace OAI

universe u_1 u_2 u_3 u_4

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.Planar
open Equiv Equiv.Perm
attribute [local simp] SameCycle.rfl
universe u
variable {α : Type u} {V : Type u_1} {F : Type u_2} {A : Type u_3} {B : Type u_4} [Fintype α] [AddCommGroup A] [AddCommGroup B]
variable {R : Ribbon α} {Inc : V → F → Prop} {ι : V → F → (A →+ B)}

theorem WeakBalanced.not_genusZero (D : WeakBalanced R Inc ι)
    (hinj : ∀ v f, Inc v f → Function.Injective (ι v f))
    (hind : ∀ v f g, Inc v f → Inc v g → f ≠ g →
      ∀ a b, ι v f a + ι v g b = 0 → a = 0)
    (hgirth : 12 ≤ (incidenceGraph Inc).egirth) : ¬ R.GenusZero := by
  classical
  intro hR
  let C : PlanarDiagram.{u} Inc ι := ⟨α, inferInstance, R, D, hR⟩
  obtain ⟨M, hmin, hvmin⟩ := C.exists_minimal
  have hnz : ∀ E : PlanarDiagram.{u} Inc ι, E.edges = M.edges →
      ∀ a, E.balanced.weight a ≠ 0 := by
    intro E hE a ha
    obtain ⟨β, iβ, S, hcard, hS, hD⟩ := E.balanced.exists_smaller E.genusZero a ha
    let E' : PlanarDiagram.{u} Inc ι := ⟨β, iβ, S, hD.some, hS⟩
    have h := hmin E'
    change M.edges ≤ Fintype.card β at h
    change Fintype.card E.Edge = M.edges at hE
    omega
  have hparallel : ∀ a b : M.Edge, M.ribbon.black.SameCycle a b →
      M.ribbon.white.SameCycle a b → a = b := by
    intro a b hb hw
    by_contra hab
    let E : PlanarDiagram.{u} Inc ι :=
      ⟨M.Edge, inferInstance, M.ribbon, M.balanced.transfer a b hb hw, M.genusZero⟩
    exact hnz E rfl a (transferWeight_zero M.balanced.weight a b hab)
  let D' := M.balanced.strong (hnz M rfl)
  have hred : D'.Reduced := by
    constructor
    · intro a ha hl
      have hw : ¬ M.ribbon.white.SameCycle a (M.ribbon.black a) := by
        intro h
        exact ha (hparallel a _ SameCycle.rfl.apply_right h).symm
      let E : PlanarDiagram.{u} Inc ι :=
        ⟨M.Edge, inferInstance, M.ribbon.mergeWhite a,
          M.balanced.mergeWhite a hw hl, M.ribbon.genusZero_mergeWhite M.genusZero a hw⟩
      have h := hvmin E rfl
      have hn : ¬ M.ribbon.white.SameCycle a (M.ribbon.face a) := by
        simpa [Ribbon.face] using hw
      have hc := swap_mul_cycles_card M.ribbon.white a (M.ribbon.face a) hn
      change Nat.card (Cycles M.ribbon.black) + Nat.card (Cycles M.ribbon.white) ≤
        Nat.card (Cycles M.ribbon.black) +
          Nat.card (Cycles (swap a (M.ribbon.face a) * M.ribbon.white)) at h
      omega
    · intro a ha hl
      have hb : ¬ M.ribbon.black.SameCycle a (M.ribbon.white a) := by
        intro h
        exact ha (hparallel a _ h SameCycle.rfl.apply_right).symm
      let E : PlanarDiagram.{u} Inc ι :=
        ⟨M.Edge, inferInstance, M.ribbon.mergeBlack a,
          M.balanced.mergeBlack a hb hl, M.ribbon.genusZero_mergeBlack M.genusZero a hb⟩
      have h := hvmin E rfl
      have hn : ¬ M.ribbon.black.SameCycle a (M.ribbon.black (M.ribbon.white a)) := by
        simpa using hb
      have hc := swap_mul_cycles_card M.ribbon.black a (M.ribbon.black (M.ribbon.white a)) hn
      change Nat.card (Cycles M.ribbon.black) + Nat.card (Cycles M.ribbon.white) ≤
        Nat.card (Cycles (swap a (M.ribbon.black (M.ribbon.white a)) * M.ribbon.black)) +
          Nat.card (Cycles M.ribbon.white) at h
      omega
  exact D'.not_genusZero hred hinj hind hgirth M.genusZero

end KaplanskyCounterexample.Planar

end

end OAI
