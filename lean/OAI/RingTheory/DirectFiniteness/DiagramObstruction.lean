import OAI.RingTheory.DirectFiniteness.OpenDiagrams

namespace OAI

universe u_1 u_2 u_3 u_4 u_5

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.Planar
open Equiv Equiv.Perm
variable {α : Type u_1} {V : Type u_2} {F : Type u_3} {A : Type u_4} {B : Type u_5} [Fintype α] [AddCommGroup A] [AddCommGroup B]

lemma Ribbon.genusZero_white_one (p : Perm α) : (Ribbon.mk p 1).GenusZero := by
  have hcomp : (Ribbon.mk p 1).components = SameCycle.setoid p := by
    unfold Ribbon.components
    apply sup_eq_left.mpr
    intro x y h
    exact (sameCycle_one.mp h).sameCycle p
  unfold Ribbon.GenusZero
  simp only [Ribbon.face, one_mul, hcomp, cycles_one_card]
  dsimp only [Cycles]
  omega

variable (Inc : V → F → Prop) (ι : V → F → (A →+ B))

omit [Fintype α] in
def OpenDiagram.initial (f₀ : F) (c : A) (hc : c ≠ 0) :
    OpenDiagram Inc ι f₀ [(f₀, c)] where
  Edge := Bool
  fintype := inferInstance
  ribbon := ⟨@List.formPerm Bool (fun a b => Classical.propDecidable (a = b)) [false, true], 1⟩
  balanced := {
    blackLabel := fun _ => none
    whiteLabel := fun _ => f₀
    blackLabel_rot := fun _ => rfl
    whiteLabel_rot := fun _ => rfl
    incident := fun _ => trivial
    weight := fun x => if x then c else 0
    exception := cycleClass 1 true
    black_sum := by intro d; simp [augMap]
    white_sum := by
      intro d hd
      induction d using Quotient.inductionOn with
      | h x =>
        change (∑ a ∈ cycleSet 1 (cycleClass 1 x), if a then c else 0) = 0
        rw [cycleSet_singleton_of_fixed 1 x rfl, Finset.sum_singleton]
        cases x
        · rfl
        · exact (hd rfl).elim
    exceptional_sum := by
      rw [cycleSet_singleton_of_fixed 1 true rfl, Finset.sum_singleton]
      exact hc }
  planar := Ribbon.genusZero_white_one _
  anchor := false
  boundary := [true]
  nodup := by decide
  rotation := fun _ _ => rfl
  exposed := by intro x; cases x <;> simp
  anchor_weight := rfl
  anchor_label := rfl
  word := rfl

variable {Inc ι}

omit [Fintype α] in
def OpenDiagram.close (f₀ : F) (D : OpenDiagram Inc ι f₀ [])
    (v₀ : V) (hv : Inc v₀ f₀) : WeakBalanced D.ribbon Inc ι := by
  have hb : D.boundary = [] := List.map_eq_nil_iff.mp D.word
  have hn (x : D.Edge) : D.balanced.blackLabel x = none ↔ x = D.anchor := by
    simpa [hb] using D.exposed x
  let bl : D.Edge → V := fun x => (D.balanced.blackLabel x).getD v₀
  have heval (x : D.Edge) : ι (bl x) (D.balanced.whiteLabel x) (D.balanced.weight x) =
      augMap ι (D.balanced.blackLabel x) (D.balanced.whiteLabel x) (D.balanced.weight x) := by
    cases h : D.balanced.blackLabel x with
    | none =>
      have hx := (hn x).mp h
      rw [hx, D.anchor_weight]
      simp
    | some v => simp [bl, h, augMap]
  exact {
    blackLabel := bl
    whiteLabel := D.balanced.whiteLabel
    blackLabel_rot := fun x => congrArg (fun v => v.getD v₀) (D.balanced.blackLabel_rot x)
    whiteLabel_rot := D.balanced.whiteLabel_rot
    incident := fun x => by
      cases h : D.balanced.blackLabel x with
      | none =>
        have hx := (hn x).mp h
        have hanc := (hn D.anchor).mpr rfl
        simpa [bl, hx, hanc, D.anchor_label] using hv
      | some v =>
        have hi := D.balanced.incident x
        simpa [augInc, bl, h] using hi
    weight := D.balanced.weight
    exception := D.balanced.exception
    black_sum := fun d => by simpa only [heval] using D.balanced.black_sum d
    white_sum := D.balanced.white_sum
    exceptional_sum := D.balanced.exceptional_sum }

omit [Fintype α] in
theorem OpenDiagram.not_empty (f₀ : F) (D : OpenDiagram Inc ι f₀ [])
    (v₀ : V) (hv : Inc v₀ f₀)
    (hinj : ∀ v f, Inc v f → Function.Injective (ι v f))
    (hind : ∀ v f g, Inc v f → Inc v g → f ≠ g →
      ∀ a b, ι v f a + ι v g b = 0 → a = 0)
    (hgirth : 12 ≤ (incidenceGraph Inc).egirth) : False :=
  (D.close f₀ v₀ hv).not_genusZero hinj hind hgirth D.planar

end KaplanskyCounterexample.Planar

end

end OAI
