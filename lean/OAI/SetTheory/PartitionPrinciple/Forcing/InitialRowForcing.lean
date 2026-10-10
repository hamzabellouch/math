import Mathlib.Algebra.Group.Subgroup.Map
import OAI.SetTheory.PartitionPrinciple.Forcing.GenericPartialFunctions
import OAI.SetTheory.PartitionPrinciple.Geometry.FinalRectangles
import OAI.SetTheory.PartitionPrinciple.Transfinite.FinalCardinality

namespace OAI


namespace PartitionPilot.Forcing.CountableCondition

universe u v w z
variable {I : Type u} {J : Type v} {K : Type w} {A : Type z}

noncomputable def rename (e : I ≃ J) (p : CountableCondition I A) : CountableCondition J A where
  value j := p.value (e.symm j)
  countable_domain := (p.countable_domain.image e).mono (by
    intro j hj
    exact ⟨e.symm j, hj, e.apply_symm_apply j⟩)

theorem rename_value (e : I ≃ J) (p : CountableCondition I A) (i : I) :
    (rename e p).value (e i) = p.value i := by
  change p.value (e.symm (e i)) = p.value i
  rw [e.symm_apply_apply]

theorem rename_refl (p : CountableCondition I A) : rename (Equiv.refl I) p = p := ext rfl

theorem rename_trans (e : I ≃ J) (f : J ≃ K) (p : CountableCondition I A) :
    rename f (rename e p) = rename (e.trans f) p := ext rfl

theorem rename_symm (e : I ≃ J) (p : CountableCondition I A) : rename e.symm (rename e p) = p := by
  apply ext
  funext i
  exact rename_value e p i

theorem rename_le_iff (e : I ≃ J) (p q : CountableCondition I A) :
    rename e p ≤ rename e q ↔ p ≤ q := by
  constructor
  · intro lower i a value
    have old : (rename e q).value (e i) = some a := (rename_value e q i).trans value
    exact (rename_value e p i).symm.trans (lower (e i) a old)
  · intro lower j a value
    exact lower (e.symm j) a value

noncomputable def renameOrderIso (e : I ≃ J) : CountableCondition I A ≃o CountableCondition J A where
  toFun := rename e
  invFun := rename e.symm
  left_inv := rename_symm e
  right_inv := rename_symm e.symm
  map_rel_iff' := rename_le_iff e _ _

theorem rename_top (e : I ≃ J) : rename (A := A) e ⊤ = ⊤ := ext rfl

theorem rename_fixed (e : I ≃ I) (p : CountableCondition I A)
    (fixed : ∀ i ∈ p.domain, e i = i) : rename e p = p := by
  apply le_antisymm
  · intro i a value
    have defined : i ∈ p.domain := by
      change p.value i ≠ none
      rw [value]
      exact Option.some_ne_none _
    have read := rename_value e p i
    rw [fixed i defined] at read
    exact read.trans value
  · intro i a value
    change p.value (e.symm i) = some a at value
    have defined : e.symm i ∈ p.domain := by
      change p.value (e.symm i) ≠ none
      rw [value]
      exact Option.some_ne_none _
    have same := fixed (e.symm i) defined
    rw [e.apply_symm_apply] at same
    exact same.symm ▸ value

end PartitionPilot.Forcing.CountableCondition



namespace PartitionPilot.Forcing

open Cardinal Compression.RecursiveMaps
open scoped Cardinal

namespace CountableCondition
universe u v
variable {I : Type u} {A : Type v}

def graphCode (p : CountableCondition I A) : Set (I × A) :=
  {ia | p.value ia.1 = some ia.2}

theorem graphCode_injective : Function.Injective (graphCode (I := I) (A := A)) := by
  intro p q eq
  apply le_antisymm
  · intro i a ha
    have mem : (i, a) ∈ q.graphCode := ha
    rw [← eq] at mem
    exact mem
  · intro i a ha
    have mem : (i, a) ∈ p.graphCode := ha
    rw [eq] at mem
    exact mem

theorem cardinal_lt (κ : Cardinal.{max u v}) (inaccessible : κ.IsInaccessible)
    (smallPairs : #(I × A) < κ) : #(CountableCondition I A) < κ :=
  (Cardinal.mk_le_of_injective graphCode_injective).trans_lt
    (SizeBounds.sets_lt κ inaccessible smallPairs)

end CountableCondition

namespace Rows
open CountableColumns
universe u

abbrev Conditions (I : Type u) := CountableCondition (I × Column) Bool

def differentRows {I : Type u} (i j : I) : Set (Conditions I) :=
  {p | ∃ α, p.value (i, α) = some false ∧ p.value (j, α) = some true}

theorem fresh_column {I : Type u} (p : Conditions I) : ∃ α : Column, ∀ i, p.value (i, α) = none := by
  classical
  let : Countable p.domain := p.countable_domain.to_subtype
  let α := upperBound (fun x : p.domain => x.val.2)
  refine ⟨α, ?_⟩
  intro i
  by_contra defined
  have impossible := upperBound_above (fun x : p.domain => x.val.2) ⟨(i, α), defined⟩
  exact lt_irrefl α impossible

theorem differentRows_dense {I : Type u} (i j : I) (ne : i ≠ j) : Dense (differentRows i j) := by
  classical
  intro p
  rcases fresh_column p with ⟨α, fresh⟩
  have ij : (i, α) ≠ (j, α) := fun eq => ne (congrArg Prod.fst eq)
  have ji : (j, α) ≠ (i, α) := Ne.symm ij
  let p1 := p.assign (i, α) false
  have p1_le : p1 ≤ p := p.assign_le (i, α) false (fresh i)
  have j_fresh : p1.value (j, α) = none :=
    (p.assign_other (i, α) (j, α) false ji).trans (fresh j)
  let q := p1.assign (j, α) true
  have q_le : q ≤ p1 := p1.assign_le (j, α) true j_fresh
  refine ⟨q, le_trans q_le p1_le, α, ?_, ?_⟩
  · exact (p1.assign_other (j, α) (i, α) true ij).trans (p.assign_same (i, α) false)
  · exact p1.assign_same (j, α) true

theorem differentRows_downwardClosed {I : Type u} (i j : I) : DownwardClosed (differentRows i j) := by
  rintro p q le ⟨α, hi, hj⟩
  exact ⟨α, le (i, α) false hi, le (j, α) true hj⟩

open MainStage.OrdinalRun

abbrev Position := {x : FinalPoint Column // x ≠ finalBottom Column}
abbrev RowForcing := Conditions Position

theorem rowForcing_countablyClosed : CountablyClosed RowForcing := CountableCondition.countablyClosed

theorem positions_cardinal_lt (κ : Cardinal.{1}) (inaccessible : κ.IsInaccessible) : #Position < κ :=
  SizeBounds.subtype_lt κ (countableOrdinalLabels_final_cardinal_bounds κ inaccessible).1 _

theorem coordinates_cardinal_lt (κ : Cardinal.{1}) (inaccessible : κ.IsInaccessible) :
    #(Position × Column) < κ :=
  SizeBounds.prod_lt κ inaccessible (positions_cardinal_lt κ inaccessible)
    (cardinal_lt_inaccessible κ inaccessible)

theorem rowForcing_cardinal_lt (κ : Cardinal.{1}) (inaccessible : κ.IsInaccessible) : #RowForcing < κ := by
  apply CountableCondition.cardinal_lt κ inaccessible
  rw [Cardinal.mk_prod, Cardinal.lift_uzero, Cardinal.mk_bool, Cardinal.lift_ofNat]
  exact Cardinal.mul_lt_of_lt inaccessible.1.le (coordinates_cardinal_lt κ inaccessible)
    ((Cardinal.natCast_lt_aleph0 (n := 2)).trans inaccessible.1)

end Rows
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.Rows

open Compression.RecursiveMaps.CountableColumns CountableCondition
universe u
variable {I : Type u}

def denseFamily (I : Type u) : Set (Set (Conditions I)) :=
  {D | (∃ c, D = definedAt c) ∨ ∃ i j, i ≠ j ∧ D = differentRows i j}

theorem denseFamily_dense {D : Set (Conditions I)} (member : D ∈ denseFamily I) : Dense D := by
  rcases member with ⟨c, rfl⟩ | ⟨i, j, ne, rfl⟩
  · exact definedAt_dense c
  · exact differentRows_dense i j ne

theorem generic_meets_coordinates (F : ConditionFilter (Conditions I))
    (generic : F.GenericFor (denseFamily I)) (c : I × Column) : F.Meets (definedAt c) :=
  generic _ (Or.inl ⟨c, rfl⟩) (definedAt_dense c)

noncomputable def row (F : ConditionFilter (Conditions I))
    (generic : F.GenericFor (denseFamily I)) (i : I) : Set Column :=
  {α | readValue F (generic_meets_coordinates F generic) (i, α) = true}

theorem mem_row_iff (F : ConditionFilter (Conditions I)) (generic : F.GenericFor (denseFamily I))
    (i : I) (α : Column) : α ∈ row F generic i ↔ ∃ p, F.mem p ∧ p.value (i, α) = some true :=
  readValue_iff F (generic_meets_coordinates F generic) (i, α) true

theorem row_injective (F : ConditionFilter (Conditions I)) (generic : F.GenericFor (denseFamily I)) :
    Function.Injective (row F generic) := by
  classical
  intro i j eq
  by_contra ne
  rcases generic _ (Or.inr ⟨i, j, ne, rfl⟩) (differentRows_dense i j ne) with ⟨p, hp, α, hi, hj⟩
  have positive : α ∈ row F generic j := (mem_row_iff F generic j α).2 ⟨p, hp, hj⟩
  have negative : α ∉ row F generic i := by
    intro member
    have value := readValue_of_condition F (generic_meets_coordinates F generic) hp hi
    change readValue F (generic_meets_coordinates F generic) (i, α) = true at member
    exact Bool.noConfusion (value.symm.trans member)
  exact negative (eq.symm ▸ positive)

theorem actual_generic_rows (F : ConditionFilter RowForcing) (generic : F.GenericFor (denseFamily Position)) :
    ∃ rows : Position → Set Column, Function.Injective rows ∧
      ∀ i α, α ∈ rows i ↔ ∃ p, F.mem p ∧ p.value (i, α) = some true :=
  ⟨row F generic, row_injective F generic, mem_row_iff F generic⟩

end PartitionPilot.Forcing.Rows



namespace PartitionPilot.Compression.RecursiveMaps.CosetGeometry.OrderAction

universe u
variable {A G : Type u} [Group G] {P : MeetOrder A} (a : OrderAction G P)

theorem act_inv_left (g : G) (x : A) : (a.iso g⁻¹).toFun ((a.iso g).toFun x) = x := by
  rw [← a.mul, inv_mul_cancel, a.one]

theorem act_inv_right (g : G) (x : A) : (a.iso g).toFun ((a.iso g⁻¹).toFun x) = x := by
  rw [← a.mul, mul_inv_cancel, a.one]

def fixSubgroup (C : A) : Subgroup G where
  carrier := {g | ∀ x, P.le x C → (a.iso g).toFun x = x}
  one_mem' := fun x _ => a.one x
  mul_mem' {g h} hg hh x lower := by rw [a.mul, hh x lower, hg x lower]
  inv_mem' {g} hg x lower := by
    apply embedding_injective (a.iso g).toMeetEmbedding
    exact (a.act_inv_right g x).trans (hg x lower).symm

theorem fix_antitone {C D : A} (lower : P.le C D) : a.fixSubgroup D ≤ a.fixSubgroup C :=
  fun _ fixed x hx => fixed x (P.trans hx lower)

def conjugateHom (g : G) : G →* G where
  toFun h := g * h * g⁻¹
  map_one' := by simp
  map_mul' h k := by simp [mul_assoc]

theorem fix_conjugation (g h : G) (C : A) :
    conjugateHom g h ∈ a.fixSubgroup ((a.iso g).toFun C) ↔ h ∈ a.fixSubgroup C := by
  constructor
  · intro fixed x lower
    apply embedding_injective (a.iso g).toMeetEmbedding
    have eq := fixed ((a.iso g).toFun x) (((a.iso g).le_iff _ _).mpr lower)
    change (a.iso (g * h * g⁻¹)).toFun ((a.iso g).toFun x) = (a.iso g).toFun x at eq
    rw [a.mul, a.mul, a.act_inv_left] at eq
    exact eq
  · intro fixed x lower
    have old : P.le ((a.iso g⁻¹).toFun x) C := by
      have h := ((a.iso g⁻¹).le_iff _ _).mpr lower
      rw [a.act_inv_left] at h
      exact h
    change (a.iso (g * h * g⁻¹)).toFun x = x
    rw [a.mul, a.mul, fixed _ old, a.act_inv_right]

def SupportedSubgroup (K : Subgroup G) : Prop := ∃ C, a.fixSubgroup C ≤ K

theorem supported_top (C : A) : a.SupportedSubgroup ⊤ := ⟨C, le_top⟩

theorem supported_upward {K H : Subgroup G} (small : a.SupportedSubgroup K) (lower : K ≤ H) :
    a.SupportedSubgroup H := by
  rcases small with ⟨C, hc⟩
  exact ⟨C, le_trans hc lower⟩

theorem supported_inf
    (bounded : ∀ C D, ∃ E, P.le C E ∧ P.le D E)
    {K H : Subgroup G} (left : a.SupportedSubgroup K) (right : a.SupportedSubgroup H) :
    a.SupportedSubgroup (K ⊓ H) := by
  rcases left with ⟨C, hc⟩
  rcases right with ⟨D, hd⟩
  rcases bounded C D with ⟨E, ce, de⟩
  exact ⟨E, le_inf (le_trans (a.fix_antitone ce) hc) (le_trans (a.fix_antitone de) hd)⟩

theorem supported_conjugate (g : G) {K : Subgroup G} (supported : a.SupportedSubgroup K) :
    a.SupportedSubgroup (K.map (conjugateHom g)) := by
  rcases supported with ⟨C, hc⟩
  refine ⟨(a.iso g).toFun C, ?_⟩
  intro h fixed
  let k := g⁻¹ * h * g
  have eq : conjugateHom g k = h := by simp [conjugateHom, k, mul_assoc]
  have old : k ∈ a.fixSubgroup C := (a.fix_conjugation g k C).mp (eq.symm ▸ fixed)
  exact Subgroup.mem_map.mpr ⟨k, hc old, eq⟩

end PartitionPilot.Compression.RecursiveMaps.CosetGeometry.OrderAction



namespace PartitionPilot.Compression.RecursiveMaps

open CosetGeometry.OrderAction
universe u v

structure NormalSubgroupFamily (G : Type u) [Group G] where
  mem : Subgroup G → Prop
  top : mem ⊤
  upward : ∀ {K H}, mem K → K ≤ H → mem H
  inf : ∀ {K H}, mem K → mem H → mem (K ⊓ H)
  conjugate : ∀ g {K}, mem K → mem (K.map (conjugateHom g))

namespace MainStage.OrdinalRun
variable (Label : Type 1)

noncomputable def supportFamily : NormalSubgroupFamily (FinalActor Label) where
  mem := (finalAction Label).SupportedSubgroup
  top := (finalAction Label).supported_top (finalBottom Label)
  upward := (finalAction Label).supported_upward
  inf := (finalAction Label).supported_inf (by
    intro C D
    rcases final_countable_upper_bound Label {C, D} ((Set.countable_singleton D).insert C) with
      ⟨E, bound⟩
    exact ⟨E, bound C (Set.mem_insert _ _),
      bound D (Set.mem_insert_of_mem _ (Set.mem_singleton D))⟩)
  conjugate := (finalAction Label).supported_conjugate

theorem supportFamily_countably_complete {I : Type v} [Countable I]
    (K : I → Subgroup (FinalActor Label)) (supported : ∀ i, (supportFamily Label).mem (K i)) :
    (supportFamily Label).mem (⨅ i, K i) := by
  classical
  change ∀ i, ∃ C, (finalAction Label).fixSubgroup C ≤ K i at supported
  choose C lower using supported
  rcases final_countable_upper_bound Label (Set.range C) (Set.countable_range C) with ⟨D, bound⟩
  refine ⟨D, le_iInf (fun i => ?_)⟩
  exact le_trans ((finalAction Label).fix_antitone (bound (C i) (Set.mem_range_self i))) (lower i)

end MainStage.OrdinalRun

end PartitionPilot.Compression.RecursiveMaps



namespace PartitionPilot.Forcing.Rows

open Compression.RecursiveMaps Compression.RecursiveMaps.CountableColumns
open Compression.RecursiveMaps.MainStage.OrdinalRun CountableCondition

theorem action_bottom (g : FinalActor Column) :
    ((finalAction Column).iso g).toFun (finalBottom Column) = finalBottom Column := by
  apply (finalOrder Column).antisymm
  · have lower := (((finalAction Column).iso g).le_iff _ _).2
      (finalBottom_least Column (((finalAction Column).iso g⁻¹).toFun (finalBottom Column)))
    rw [(finalAction Column).act_inv_right] at lower
    exact lower
  · exact finalBottom_least Column _

noncomputable def positionAction (g : FinalActor Column) (i : Position) : Position :=
  ⟨((finalAction Column).iso g).toFun i.val, by
    intro eq
    apply i.property
    exact Compression.embedding_injective ((finalAction Column).iso g).toMeetEmbedding
      (eq.trans (action_bottom g).symm)⟩

theorem positionAction_one (i : Position) : positionAction 1 i = i :=
  Subtype.ext ((finalAction Column).one i.val)

theorem positionAction_mul (g h : FinalActor Column) (i : Position) :
    positionAction (g * h) i = positionAction g (positionAction h i) :=
  Subtype.ext ((finalAction Column).mul g h i.val)

noncomputable def positionPermutation (g : FinalActor Column) : Position ≃ Position where
  toFun := positionAction g
  invFun := positionAction g⁻¹
  left_inv i := Subtype.ext ((finalAction Column).act_inv_left g i.val)
  right_inv i := Subtype.ext ((finalAction Column).act_inv_right g i.val)

noncomputable def coordinatePermutation (g : FinalActor Column) : Position × Column ≃ Position × Column :=
  Equiv.prodCongr (positionPermutation g) (Equiv.refl Column)

theorem coordinatePermutation_one : coordinatePermutation 1 = Equiv.refl (Position × Column) := by
  apply Equiv.ext
  intro x
  exact Prod.ext (positionAction_one x.1) rfl

theorem coordinatePermutation_mul (g h : FinalActor Column) :
    coordinatePermutation (g * h) = (coordinatePermutation h).trans (coordinatePermutation g) := by
  apply Equiv.ext
  intro x
  exact Prod.ext (positionAction_mul g h x.1) rfl

noncomputable def rowAction (g : FinalActor Column) : RowForcing ≃o RowForcing :=
  renameOrderIso (coordinatePermutation g)

theorem rowAction_one (p : RowForcing) : rowAction 1 p = p := by
  change rename (coordinatePermutation 1) p = p
  rw [coordinatePermutation_one, rename_refl]

theorem rowAction_mul (g h : FinalActor Column) (p : RowForcing) :
    rowAction (g * h) p = rowAction g (rowAction h p) := by
  change rename (coordinatePermutation (g * h)) p =
    rename (coordinatePermutation g) (rename (coordinatePermutation h) p)
  rw [coordinatePermutation_mul, rename_trans]

theorem rowAction_value (g : FinalActor Column) (p : RowForcing) (i : Position) (α : Column) :
    (rowAction g p).value (positionAction g i, α) = p.value (i, α) :=
  rename_value (coordinatePermutation g) p (i, α)

theorem rowAction_top (g : FinalActor Column) : rowAction g ⊤ = ⊤ :=
  rename_top (coordinatePermutation g)

theorem rowAction_le_iff (g : FinalActor Column) (p q : RowForcing) :
    rowAction g p ≤ rowAction g q ↔ p ≤ q :=
  rename_le_iff (coordinatePermutation g) p q

theorem rowCondition_supported (p : RowForcing) :
    ∃ C : FinalPoint Column, ∀ g : FinalActor Column,
      g ∈ (finalAction Column).fixSubgroup C → rowAction g p = p := by
  let positions : Set (FinalPoint Column) := (fun c : Position × Column => c.1.val) '' p.domain
  have small : positions.Countable := p.countable_domain.image (fun c => c.1.val)
  rcases final_countable_upper_bound Column positions small with ⟨C, bound⟩
  refine ⟨C, ?_⟩
  intro g fixed
  apply rename_fixed
  intro c hc
  apply Prod.ext
  · apply Subtype.ext
    exact fixed c.1.val (bound c.1.val ⟨c, hc, rfl⟩)
  · rfl

end PartitionPilot.Forcing.Rows



namespace PartitionPilot.Forcing.Rows

open Cardinal Compression.RecursiveMaps Compression.RecursiveMaps.CountableColumns
open Compression.RecursiveMaps.MainStage.OrdinalRun SetRealization
open scoped Cardinal

noncomputable def rowConditionPresentation : Presentation RowForcing := Presentation.canonical RowForcing

theorem rowConditionPresentation_rank_lt (κ : Cardinal.{1}) (inaccessible : κ.IsInaccessible) :
    ZFSet.rank rowConditionPresentation.carrier < κ.ord :=
  Presentation.canonical_rank_lt _ κ (rowForcing_cardinal_lt κ inaccessible)

structure InitialRowForcingLaws (κ : Cardinal.{1}) : Prop where
  closed : CountablyClosed RowForcing
  small : #RowForcing < κ
  rank : ZFSet.rank rowConditionPresentation.carrier < κ.ord
  coordinate_dense : ∀ c : Position × Column, Dense (CountableCondition.definedAt (A := Bool) c)
  different_dense : ∀ i j : Position, i ≠ j → Dense (differentRows i j)
  countable_decisions : ∀ (A : Nat → Type 1) (d : DecisionSystem RowForcing A), Dense d.commonDecisions
  action_one : ∀ p, rowAction 1 p = p
  action_mul : ∀ g h p, rowAction (g * h) p = rowAction g (rowAction h p)
  action_value : ∀ g p i α, (rowAction g p).value (positionAction g i, α) = p.value (i, α)
  condition_support : ∀ p, ∃ C : FinalPoint Column, ∀ g : FinalActor Column,
    g ∈ (finalAction Column).fixSubgroup C → rowAction g p = p
  generic_rows : ∀ F : ConditionFilter RowForcing, F.GenericFor (denseFamily Position) →
    ∃ rows : Position → Set Column, Function.Injective rows ∧
      ∀ i α, α ∈ rows i ↔ ∃ p, F.mem p ∧ p.value (i, α) = some true

theorem initial_row_forcing_laws (κ : Cardinal.{1}) (inaccessible : κ.IsInaccessible) :
    InitialRowForcingLaws κ where
  closed := rowForcing_countablyClosed
  small := rowForcing_cardinal_lt κ inaccessible
  rank := rowConditionPresentation_rank_lt κ inaccessible
  coordinate_dense := CountableCondition.definedAt_dense
  different_dense := differentRows_dense
  countable_decisions := fun _ d => d.commonDecisions_dense rowForcing_countablyClosed
  action_one := rowAction_one
  action_mul := rowAction_mul
  action_value := rowAction_value
  condition_support := rowCondition_supported
  generic_rows := actual_generic_rows

end PartitionPilot.Forcing.Rows

end OAI
