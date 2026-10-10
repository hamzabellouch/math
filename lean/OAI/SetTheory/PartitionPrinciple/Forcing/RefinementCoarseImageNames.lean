import OAI.SetTheory.PartitionPrinciple.Definability.EquivalenceClassCodes
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundNiceNameNormalization

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u v

noncomputable def coarseClassImage (U sigma Rc : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ y ∈ sigma, y ∈ U ∧ ZFSet.pair z y ∈ Rc) U

theorem mem_coarseClassImage (U sigma Rc z : ZFSet.{u}) :
    z ∈ coarseClassImage U sigma Rc ↔
      z ∈ U ∧ ∃ y ∈ sigma, y ∈ U ∧ ZFSet.pair z y ∈ Rc := ZFSet.mem_sep

theorem coarseClassImage_of_fineClass {U Rf Rc x : ZFSet.{u}}
    (fine : EquivalenceRelationCode U Rf) (coarse : EquivalenceRelationCode U Rc)
    (refinement : Rf ⊆ Rc) (hx : x ∈ U) :
    coarseClassImage U (equivalenceClass U Rf x) Rc = equivalenceClass U Rc x := by
  apply ZFSet.ext
  intro z
  rw [mem_coarseClassImage, mem_equivalenceClass]
  constructor
  · rintro ⟨hz, y, hy, _, related⟩
    exact ⟨hz, coarse.trans z y x related (refinement ((mem_equivalenceClass U Rf x y).1 hy).2)⟩
  · rintro ⟨hz, related⟩
    exact ⟨hz, x, fine.class_self hx, hx, related⟩

namespace BoundedFormula

def coarseClassImageFormula : BoundedFormula 4 :=
  .conj (.mem 0 1) (exMem 2 (.conj (.mem 0 2) (pairMembershipFormula 1 0 4)))

theorem truth_coarseClassImageFormula (env : Fin 4 → ZFSet.{u}) :
    Truth coarseClassImageFormula env ↔ env 0 ∈ coarseClassImage (env 1) (env 2) (env 3) := by
  rw [mem_coarseClassImage]
  change (env 0 ∈ env 1 ∧ Truth (exMem 2 (.conj (.mem 0 2) (pairMembershipFormula 1 0 4))) env) ↔ _
  rw [truth_exMem]
  exact and_congr_right (fun _ => exists_congr (fun y => and_congr_right (fun _ =>
    and_congr_right (fun _ => truth_pairMembershipFormula 1 0 4 (extend y env)))))

end BoundedFormula

namespace Name
variable {P : Type u} [PartialOrder P] [OrderTop P] {s : Presentation P}

noncomputable def refinementCoarseImage (D : NameDomain s) (T : ZFSet.{u})
    (valid : ∀ z ∈ T, IsName s z) (U sigma Rc : D.names) : Name s :=
  separationName D BoundedFormula.coarseClassImageFormula.toFormula
    (extend U (extend sigma (extend Rc Fin.elim0))) (familySet ⊤ T valid)

theorem entry_refinementCoarseImage (D : NameDomain s) (T : ZFSet.{u})
    (valid : ∀ z ∈ T, IsName s z) (U sigma Rc : D.names) (z : Name s) (p : P) :
    Entry z (refinementCoarseImage D T valid U sigma Rc) p ↔
      z.val ∈ T ∧ ∃ h : z ∈ D.names,
        Forces D BoundedFormula.coarseClassImageFormula.toFormula
          (extend ⟨z, h⟩ (extend U (extend sigma (extend Rc Fin.elim0)))) p := by
  rw [refinementCoarseImage, entry_separationName]
  constructor
  · rintro ⟨r, entry, _, forced⟩
    exact ⟨((entry_familySet ⊤ T valid z r).1 entry).1, forced⟩
  · rintro ⟨hz, forced⟩
    exact ⟨⊤, (entry_familySet ⊤ T valid z ⊤).2 ⟨hz, rfl⟩, le_top, forced⟩

theorem eval_refinementCoarseImage (D : NameDomain s) (T : ZFSet.{u})
    (valid : ∀ z ∈ T, IsName s z) (U sigma Rc : D.names)
    (family : familySet ⊤ T valid ∈ D.names) (H : ConditionFilter P)
    (generic : H.GenericFor (formulaFamily D)) :
    eval {p | H.mem p} (refinementCoarseImage D T valid U sigma Rc) =
      coarseClassImage (eval {p | H.mem p} U.val) (eval {p | H.mem p} sigma.val)
        (eval {p | H.mem p} Rc.val) ∩ eval {p | H.mem p} (familySet ⊤ T valid) := by
  rw [refinementCoarseImage, eval_separationName D H generic _ _ family]
  let evaluated : TransitiveGround.{u} := ⟨D.values {p | H.mem p}, D.values_transitive _⟩
  apply ZFSet.ext
  intro x
  rw [ZFSet.mem_sep, ZFSet.mem_inter]
  constructor
  · rintro ⟨hx, formula⟩
    have members : ∀ j, extend x (evalAssignment {p | H.mem p}
        (extend U (extend sigma (extend Rc Fin.elim0)))) j ∈ D.values {p | H.mem p} :=
      Fin.cases ((D.values_transitive _ (show eval {p | H.mem p} (familySet ⊤ T valid) ∈ D.values {p | H.mem p} from ⟨⟨_, family⟩, rfl⟩)) hx)
        (fun j => ⟨(extend U (extend sigma (extend Rc Fin.elim0))) j, rfl⟩)
    have truth := (BoundedFormula.realize_toFormula evaluated BoundedFormula.coarseClassImageFormula _ members).1 formula
    exact ⟨(BoundedFormula.truth_coarseClassImageFormula _).1 truth, hx⟩
  · rintro ⟨member, hx⟩
    have members : ∀ j, extend x (evalAssignment {p | H.mem p}
        (extend U (extend sigma (extend Rc Fin.elim0)))) j ∈ D.values {p | H.mem p} :=
      Fin.cases ((D.values_transitive _ (show eval {p | H.mem p} (familySet ⊤ T valid) ∈ D.values {p | H.mem p} from ⟨⟨_, family⟩, rfl⟩)) hx)
        (fun j => ⟨(extend U (extend sigma (extend Rc Fin.elim0))) j, rfl⟩)
    exact ⟨hx, (BoundedFormula.realize_toFormula evaluated BoundedFormula.coarseClassImageFormula _ members).2
      ((BoundedFormula.truth_coarseClassImageFormula (extend x (evalAssignment {p | H.mem p}
        (extend U (extend sigma (extend Rc Fin.elim0)))))).2 member)⟩

theorem eval_refinementCoarseImage_of_subset (D : NameDomain s) (T : ZFSet.{u})
    (valid : ∀ z ∈ T, IsName s z) (U sigma Rc : D.names)
    (family : familySet ⊤ T valid ∈ D.names) (H : ConditionFilter P)
    (generic : H.GenericFor (formulaFamily D))
    (subset : eval {p | H.mem p} U.val ⊆ eval {p | H.mem p} (familySet ⊤ T valid)) :
    eval {p | H.mem p} (refinementCoarseImage D T valid U sigma Rc) =
      coarseClassImage (eval {p | H.mem p} U.val) (eval {p | H.mem p} sigma.val)
        (eval {p | H.mem p} Rc.val) := by
  rw [eval_refinementCoarseImage D T valid U sigma Rc family H generic]
  apply ZFSet.ext
  intro x
  exact ⟨fun h => (ZFSet.mem_inter.1 h).1,
    fun h => ZFSet.mem_inter.2 ⟨h, subset ((mem_coarseClassImage _ _ _ _).1 h).1⟩⟩

variable {G : Type v} [Group G] (a : PosetAction G P)

theorem refinementCoarseImage_support (D : NameDomain s)
    (closed : ∀ g z, z ∈ D.names → a.act s g z ∈ D.names)
    (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
    (terms : ∀ g (z : Name s), z.val ∈ T → (a.act s g z).val ∈ T)
    (U sigma Rc : D.names) (K : Subgroup G)
    (domain : K ≤ a.stabilizer s U.val) (witness : K ≤ a.stabilizer s sigma.val)
    (relation : K ≤ a.stabilizer s Rc.val) :
    K ≤ a.stabilizer s (refinementCoarseImage D T valid U sigma Rc) := by
  intro g hg
  change a.act s g (refinementCoarseImage D T valid U sigma Rc) = _
  unfold refinementCoarseImage
  rw [a.act_separationName s D closed, act_familySet a T valid terms]
  have env : a.actAssignment s D closed g (extend U (extend sigma (extend Rc Fin.elim0))) =
      extend U (extend sigma (extend Rc Fin.elim0)) := by
    funext j
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i))) j
    · exact Subtype.ext (domain hg)
    · exact Subtype.ext (witness hg)
    · exact Subtype.ext (relation hg)
  rw [env]

end Name

end PartitionPilot.Forcing

end

end OAI
