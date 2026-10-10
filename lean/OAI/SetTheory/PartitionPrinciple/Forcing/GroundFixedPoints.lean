import OAI.SetTheory.PartitionPrinciple.Definability.UnionEntryFormula

namespace OAI

section

namespace PartitionPilot.Forcing.SetFormula

universe u

def postfixedFormula {k : Nat} (φ : SetFormula (k + 2)) : SetFormula (k + 1) :=
  .all (imp (.mem 0 1) φ)

def definableOperator {k : Nat} (U : Set ZFSet.{u}) (φ : SetFormula (k + 2))
    (params : Fin k → ZFSet.{u}) (B S : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun x => Realize U φ (extend x (extend S params))) B

theorem definableOperator_subset {k : Nat} (U : Set ZFSet.{u}) (φ : SetFormula (k + 2))
    (params : Fin k → ZFSet.{u}) (B S : ZFSet.{u}) : definableOperator U φ params B S ⊆ B :=
  fun _ hx => (ZFSet.mem_sep.1 hx).1

end PartitionPilot.Forcing.SetFormula

namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem realize_postfixedFormula {k : Nat} (φ : SetFormula (k + 2))
    (params : Fin k → ZFSet.{u}) {B S : ZFSet.{u}}
    (hS : S ∈ M.sets) (bound : S ⊆ B) :
    Realize M.sets (postfixedFormula φ) (extend S params) ↔
      S ⊆ definableOperator M.sets φ params B S := by
  simp only [postfixedFormula, Realize, realize_imp]
  constructor
  · intro h x hx
    exact ZFSet.mem_sep.2 ⟨bound hx, h x (M.transitive hS hx) hx⟩
  · intro h x _ hx
    exact (ZFSet.mem_sep.1 (h hx)).2

theorem definableOperator_mem (separation : SeparationSchema M.sets)
    {k : Nat} (φ : SetFormula (k + 2)) (params : Fin k → ZFSet.{u})
    (members : ∀ i, params i ∈ M.sets) {B S : ZFSet.{u}}
    (hB : B ∈ M.sets) (hS : S ∈ M.sets) : definableOperator M.sets φ params B S ∈ M.sets :=
  M.separation_mem separation φ (extend S params) (fun i => Fin.cases hS members i) hB

theorem exists_greatest_definable_fixedPoint
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {k : Nat} (φ : SetFormula (k + 2)) (params : Fin k → ZFSet.{u})
    (members : ∀ i, params i ∈ M.sets) {B : ZFSet.{u}} (hB : B ∈ M.sets)
    (mono : ∀ S ∈ M.sets, ∀ T ∈ M.sets, S ⊆ B → T ⊆ B → S ⊆ T →
      definableOperator M.sets φ params B S ⊆ definableOperator M.sets φ params B T) :
    ∃ R ∈ M.sets, R ⊆ B ∧ definableOperator M.sets φ params B R = R ∧
      ∀ S ∈ M.sets, S ⊆ B → S ⊆ definableOperator M.sets φ params B S → S ⊆ R := by
  let F := definableOperator M.sets φ params B
  obtain ⟨W, hW, subsets⟩ := M.power_witness powers hB
  let C := ZFSet.sep (fun S => Realize M.sets (postfixedFormula φ) (extend S params)) W
  have hC : C ∈ M.sets := M.separation_mem separation (postfixedFormula φ) params members hW
  let R := ZFSet.sUnion C
  have hR : R ∈ M.sets := M.union_mem unions hC
  have memC : ∀ S, S ∈ C ↔ S ∈ M.sets ∧ S ⊆ B ∧ S ⊆ F S := by
    intro S
    constructor
    · intro h
      obtain ⟨hSW, post⟩ := ZFSet.mem_sep.1 h
      have hSM := M.transitive hW hSW
      have hSB := (subsets S hSM).1 hSW
      exact ⟨hSM, hSB, (M.realize_postfixedFormula φ params hSM hSB).1 post⟩
    · rintro ⟨hSM, hSB, post⟩
      exact ZFSet.mem_sep.2 ⟨(subsets S hSM).2 hSB,
        (M.realize_postfixedFormula φ params hSM hSB).2 post⟩
  have hRB : R ⊆ B := by
    intro x hx
    obtain ⟨S, hS, hxS⟩ := ZFSet.mem_sUnion.1 hx
    exact ((memC S).1 hS).2.1 hxS
  have greatest : ∀ S ∈ M.sets, S ⊆ B → S ⊆ F S → S ⊆ R := by
    intro S hS hSB post x hx
    exact ZFSet.mem_sUnion.2 ⟨S, (memC S).2 ⟨hS, hSB, post⟩, hx⟩
  have postR : R ⊆ F R := by
    intro x hx
    obtain ⟨S, hSC, hxS⟩ := ZFSet.mem_sUnion.1 hx
    obtain ⟨hS, hSB, post⟩ := (memC S).1 hSC
    exact mono S hS R hR hSB hRB (greatest S hS hSB post) (post hxS)
  have hFR : F R ∈ M.sets := M.definableOperator_mem separation φ params members hB hR
  have hFRB : F R ⊆ B := definableOperator_subset M.sets φ params B R
  have postFR : F R ⊆ F (F R) := mono R hR (F R) hFR hRB hFRB postR
  have fixed : F R = R := ZFSet.ext fun _ =>
    ⟨fun hx => greatest (F R) hFR hFRB postFR hx, fun hx => postR hx⟩
  exact ⟨R, hR, hRB, fixed, greatest⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
