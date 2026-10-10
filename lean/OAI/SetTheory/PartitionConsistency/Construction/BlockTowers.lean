import Mathlib
import OAI.SetTheory.PartitionConsistency.Construction.CellReorder
import OAI.SetTheory.PartitionConsistency.Construction.SaturatedMonoids

namespace OAI

/-! ## BlockIndex -/

/-! Lexicographic concatenation of the actual rounds. The extra cut at the
end of each round is retained, making passage to the next initial cut an
identity step. -/
namespace PartitionConsistency.ConservativeMonoids
universe u
noncomputable section
open scoped Classical
namespace BlockIndex
variable {I : Type u} {J : I → Type u}
variable [LinearOrder I] [WellFoundedLT I] [OrderBot I] [NoMaxOrder I] [SuccOrder I]
variable [∀ i, LinearOrder (J i)] [∀ i, WellFoundedLT (J i)]
variable [∀ i, OrderBot (J i)] [∀ i, OrderTop (J i)] [∀ i, SuccOrder (J i)]

abbrev Interior (I : Type u) (J : I → Type u) := Lex (Sigma J)
abbrev Index (I : Type u) (J : I → Type u) := WithTop (Interior I J)

instance : WellFoundedLT (Interior I J) := by
  constructor
  rintro ⟨i,j⟩
  induction i using (wellFounded_lt (α := I)).induction with
  | h i ih =>
    induction j using (wellFounded_lt (α := J i)).induction with
    | h j jh =>
      constructor
      rintro ⟨k,l⟩ hl
      cases hl with
      | left _ _ hk => exact ih k hk l
      | right _ _ hl => exact jh l hl

instance : SuccOrder (Index I J) := SuccOrder.ofLinearWellFoundedLT _

def cut (i : I) (j : J i) : Index I J := WithTop.some (toLex ⟨i,j⟩)

section
omit [WellFoundedLT I] [OrderBot I] [NoMaxOrder I] [SuccOrder I]
  [∀ i, WellFoundedLT (J i)] [∀ i, OrderBot (J i)] [∀ i, OrderTop (J i)]
  [∀ i, SuccOrder (J i)]

@[simp] theorem cut_le_cut (i : I) (j k : J i) : cut i j ≤ cut i k ↔ j ≤ k := by
  simp [cut, Sigma.Lex.le_def]
  change (i < i ∨ i = i ∧ j ≤ k) ↔ j ≤ k
  simp
@[simp] theorem cut_lt_cut (i : I) (j k : J i) : cut i j < cut i k ↔ j < k := by
  simp [cut, Sigma.Lex.lt_def]
  change (i < i ∨ i = i ∧ j < k) ↔ j < k
  simp
theorem cut_lt_of_lt {i k : I} (h : i < k) (j : J i) (l : J k) : cut i j < cut k l :=
  WithTop.coe_lt_coe.mpr (Sigma.Lex.left _ _ h)
@[simp] theorem cut_lt_top (i : I) (j : J i) : cut i j < ⊤ := WithTop.coe_lt_top _
end

omit [WellFoundedLT I] [NoMaxOrder I] [SuccOrder I]
  [∀ i, WellFoundedLT (J i)] [∀ i, OrderTop (J i)] [∀ i, SuccOrder (J i)] in
@[simp] theorem cut_bot : cut (⊥ : I) (⊥ : J ⊥) = (⊥ : Index I J) := rfl

omit [OrderBot I] [NoMaxOrder I] [SuccOrder I] [∀ i, OrderBot (J i)] in
/-- Successors within a block. -/
theorem succ_inner (i : I) (j : J i) (hj : j < ⊤) :
    Order.succ (cut i j) = cut i (Order.succ j) := by
  apply CovBy.succ_eq
  apply WithTop.coe_covBy_coe.mpr
  have H := Order.covBy_succ_of_not_isMax (not_isMax_iff_ne_top.mpr hj.ne)
  refine ⟨Sigma.Lex.right _ _ H.lt,?_⟩
  rintro ⟨k,l⟩ h₁ h₂
  cases h₁ with
  | left _ _ h₁ =>
    cases h₂ with
    | left _ _ h₂ => exact h₁.not_gt h₂
    | right _ _ _ => exact lt_irrefl _ h₁
  | right _ _ h₁ =>
    cases h₂ with
    | left _ _ h₂ => exact lt_irrefl _ h₂
    | right _ _ h₂ => exact H.2 h₁ h₂

omit [OrderBot I] [∀ i, SuccOrder (J i)] in
/-- The final cut of one block is followed by the initial cut of the next. -/
theorem succ_boundary (i : I) :
    Order.succ (cut i (⊤ : J i)) = cut (Order.succ i) (⊥ : J (Order.succ i)) := by
  apply CovBy.succ_eq
  apply WithTop.coe_covBy_coe.mpr
  refine ⟨Sigma.Lex.left _ _ (Order.lt_succ i),?_⟩
  rintro ⟨k,l⟩ h₁ h₂
  cases h₁ with
  | left _ _ h₁ =>
    cases h₂ with
    | left _ _ h₂ => exact (Order.covBy_succ i).2 h₁ h₂
    | right _ _ h₂ => exact not_lt_bot h₂
  | right _ _ h₁ => exact not_top_lt h₁

omit [OrderBot I] [NoMaxOrder I] [SuccOrder I] in
/-- A noninitial limit inside a block must be a limit of that block. -/
theorem inner_limit {i : I} {j : J i} (h : Order.IsSuccLimit (cut i j)) (hj : j ≠ ⊥) :
    Order.IsSuccLimit j := by
  refine ⟨not_isMin_iff_ne_bot.mpr hj,?_⟩
  intro k hk
  have hkt : k < ⊤ := hk.lt.trans_le le_top
  have he := succ_inner i k hkt
  rw [hk.succ_eq] at he
  exact (not_isMax_iff_ne_top.mpr (cut_lt_top i k).ne) ((he ▸ h).isMax)

omit [∀ i, SuccOrder (J i)] in
/-- A limit at an initial cut must be an outer limit (not a successor or
zero). This includes the identity boundary cuts in the argument. -/
theorem outer_limit {i : I} (h : Order.IsSuccLimit (cut i (⊥ : J i))) :
    Order.IsSuccLimit i := by
  refine ⟨?_,?_⟩
  · intro hi
    have hi' := hi.eq_bot
    subst i
    exact h.ne_bot cut_bot
  · intro k hk
    have he := succ_boundary (J := J) k
    rw [hk.succ_eq] at he
    exact (not_isMax_iff_ne_top.mpr (cut_lt_top k (⊤ : J k)).ne) ((he ▸ h).isMax)

end BlockIndex
end
end PartitionConsistency.ConservativeMonoids


/-! ## BlockTower -/

namespace PartitionConsistency.ConservativeMonoids
universe u
noncomputable section
open scoped Classical
open BlockIndex
variable {I : Type u} {J : I → Type u}
variable [LinearOrder I] [WellFoundedLT I] [OrderBot I] [NoMaxOrder I] [SuccOrder I]
variable [∀ i, LinearOrder (J i)] [∀ i, WellFoundedLT (J i)]
variable [∀ i, OrderBot (J i)] [∀ i, OrderTop (J i)] [∀ i, SuccOrder (J i)]
variable (T : Object.{u})

/-- An iterated cellular construction before flattening. All stages are
literal submonoids of the same final monoid. -/
structure BlockTower where
  stage : ∀ i, J i → Subobject T
  inner_mono : ∀ i, Monotone (fun j => (stage i j).submonoid)
  outer_mono : Monotone (fun i => (stage i ⊥).submonoid)
  boundary : ∀ i, (stage i ⊤).submonoid = (stage (Order.succ i) ⊥).submonoid
  inner_limit : ∀ i j, Order.IsSuccLimit j → ∀ x, x ∈ (stage i j).submonoid →
    ∃ k < j, x ∈ (stage i k).submonoid
  outer_limit : ∀ i, Order.IsSuccLimit i → ∀ x, x ∈ (stage i ⊥).submonoid →
    ∃ k < i, x ∈ (stage k ⊥).submonoid
  covers : ∀ x : T, ∃ i, x ∈ (stage i ⊥).submonoid
  step : ∀ i j, j < ⊤ → Nonempty (Attachment (stage i j) (stage i (Order.succ j)))

namespace BlockTower
variable {T} (B : BlockTower (I := I) (J := J) T)

def flatStage : Index I J → Subobject T
  | none => Subobject.top
  | some z => B.stage z.1 z.2

omit [WellFoundedLT I] [OrderBot I] [NoMaxOrder I] [∀ i, WellFoundedLT (J i)] in
@[simp] theorem flatStage_cut (i : I) (j : J i) : B.flatStage (cut i j) = B.stage i j := rfl

/-- Flattening retains every original cell and does not change the terminal
monoid or any of the limit unions. -/
def flatten : CellTower T (Index I J) where
  stage := B.flatStage
  terminal := rfl
  mono := by
    intro a b hab
    cases b with
    | none => exact le_top
    | some b =>
      cases a with
      | none => exact (WithTop.not_top_le_coe _ hab).elim
      | some a =>
        rcases a with ⟨i,j⟩
        rcases b with ⟨k,l⟩
        have h := WithTop.coe_le_coe.mp hab
        cases h with
        | left _ _ hik =>
          change (B.stage i j).submonoid ≤ (B.stage k l).submonoid
          calc
            (B.stage i j).submonoid ≤ (B.stage i ⊤).submonoid := B.inner_mono i le_top
            _ = (B.stage (Order.succ i) ⊥).submonoid := B.boundary i
            _ ≤ (B.stage k ⊥).submonoid := B.outer_mono (Order.succ_le_of_lt hik)
            _ ≤ (B.stage k l).submonoid := B.inner_mono k bot_le
        | right _ _ hjl => exact B.inner_mono i hjl
  continuous := by
    intro a ha x hx
    cases a with
    | none =>
      obtain ⟨i,hi⟩ := B.covers x
      exact ⟨cut i ⊥,cut_lt_top _ _,hi⟩
    | some a =>
      rcases a with ⟨i,j⟩
      change Order.IsSuccLimit (cut i j) at ha
      by_cases hj : j = ⊥
      · subst j
        obtain ⟨k,hki,hkx⟩ := B.outer_limit i (BlockIndex.outer_limit ha) x hx
        exact ⟨cut k ⊥,cut_lt_of_lt hki _ _,hkx⟩
      · obtain ⟨k,hkj,hkx⟩ := B.inner_limit i j (BlockIndex.inner_limit ha hj) x hx
        exact ⟨cut i k,(cut_lt_cut i k j).mpr hkj,hkx⟩
  step := by
    intro a
    cases a with
    | none =>
      left
      change (B.flatStage (⊤ : Index I J)).submonoid =
        (B.flatStage (Order.succ (⊤ : Index I J))).submonoid
      rw [Order.succ_top]
    | some a =>
      rcases a with ⟨i,j⟩
      change (B.flatStage (cut i j)).submonoid =
        (B.flatStage (Order.succ (cut i j))).submonoid ∨
        Nonempty (Attachment (B.flatStage (cut i j)) (B.flatStage (Order.succ (cut i j))))
      by_cases hj : j = ⊤
      · subst j
        left
        rw [succ_boundary, flatStage_cut,flatStage_cut]
        exact B.boundary i
      · right
        rw [succ_inner i j (lt_top_iff_ne_top.mpr hj),flatStage_cut,flatStage_cut]
        exact B.step i j (lt_top_iff_ne_top.mpr hj)

@[simp] theorem flatten_bottom : (B.flatten.stage ⊥) = B.stage ⊥ ⊥ := rfl

end BlockTower
end
end PartitionConsistency.ConservativeMonoids


/-! ## RangeAttachment -/

namespace PartitionConsistency.ConservativeMonoids
universe u
open CategoryTheory DiagramOrder
noncomputable section

namespace Cell
variable {M N : Object.{u}} (d : Cell M)

theorem simulation_surjective (f : M ⟶ N) (hf : Function.Surjective f) :
    Function.Surjective (d.simulation f) := by
  apply (MonoidHom.mrange_eq_top (f := (d.simulation f).toMonoidHom)).mp
  apply (d.map f).generated
  · intro y
    obtain ⟨x,rfl⟩ := hf y
    exact ⟨d.inclusion x,Cell.simulation_old d f x⟩
  · intro i
    have hi : (d.map f).generator i ∈ Set.range (d.map f).generator := ⟨i,rfl⟩
    rw [← d.simulation_generator_range f] at hi
    obtain ⟨j,hj⟩ := hi
    exact ⟨d.generator j,hj⟩

def simulationEquiv (f : M ⟶ N) (hf : Function.Surjective f) :
    d.extension ≃* (d.map f).extension :=
  MulEquiv.ofBijective (d.simulation f).toMonoidHom
    ⟨(d.simulation f).injective,d.simulation_surjective f hf⟩

@[simp] theorem simulationEquiv_old (f : M ⟶ N) (hf : Function.Surjective f) (x : M) :
    d.simulationEquiv f hf (d.inclusion x) = (d.map f).inclusion (f x) :=
  Cell.simulation_old d f x

/-- Identify an original executed cell with the literal ranges inside its
terminal monoid. Surjectivity here is proved from the presentation. -/
def rangeAttachment {T : Object.{u}} (f : M ⟶ T) (g : d.extension ⟶ T)
    (h : ∀ x, g (d.inclusion x) = f x) :
    Attachment (Subobject.range f) (Subobject.range g) := by
  let e := ofMulEquiv f.rangeEquiv
  let s := d.simulationEquiv e f.rangeEquiv.surjective
  refine ⟨d.map e,s.symm.trans g.rangeEquiv,?_⟩
  intro y
  obtain ⟨x,rfl⟩ := f.rangeEquiv.surjective y
  change g (s.symm ((d.map e).inclusion (e x))) = f x
  rw [← d.simulationEquiv_old e f.rangeEquiv.surjective x,s.symm_apply_apply]
  exact h x

end Cell

namespace Hom
variable {M N T : Object.{u}} (f : M ⟶ N) (g : N ⟶ T)

theorem range_comp_of_surjective (hf : Function.Surjective f) :
    Subobject.range (g.comp f) = Subobject.range g := by
  apply Subobject.ext
  apply le_antisymm
  · rintro y ⟨x,rfl⟩
    exact ⟨f x,rfl⟩
  · rintro y ⟨x,rfl⟩
    obtain ⟨z,rfl⟩ := hf x
    exact ⟨z,rfl⟩

end Hom
end
end PartitionConsistency.ConservativeMonoids


/-! ## SaturationBlock -/

namespace PartitionConsistency.ConservativeMonoids
universe u
open CategoryTheory DiagramOrder
noncomputable section

/-- The literal range of an executed request is the range attachment of
its actual probe or merger presentation. -/
theorem request_rangeAttachment {M : MonoidConstruction.Object.{u}} {T : Object.{u}}
    (d : MonoidConstruction.Request M) (f : forgetMargins.obj M ⟶ T)
    (g : forgetMargins.obj d.target ⟶ T) (h : ∀ x, g (d.inclusion x) = f x) :
    Nonempty (Attachment (Subobject.range f) (Subobject.range g)) := by
  cases d with
  | inl d => exact ⟨(RequestCell (.inl d)).rangeAttachment f g h⟩
  | inr d => exact ⟨(RequestCell (.inr d)).rangeAttachment f g h⟩

end
end PartitionConsistency.ConservativeMonoids

namespace PartitionConsistency.MonoidConstruction
universe u
open CategoryTheory DiagramOrder ConservativeMonoids
noncomputable section
open scoped Classical

namespace RoundOrdinal
instance : SuccOrder RoundOrdinal.{u} := SuccOrder.ofLinearWellFoundedLT _
end RoundOrdinal

namespace Saturation
variable (M : Object.{u}) (K : Type u) [Nonempty K]

abbrev blockBase (i : RoundOrdinal.{u}) := (tower M K).obj (i : OuterIndex)
abbrev blockIndex (i : RoundOrdinal.{u}) := CompleteRound.Index (blockBase M K i) K
abbrev blockFunctor (i : RoundOrdinal.{u}) := CompleteRound.tower (blockBase M K i) K

def blockMap (i : RoundOrdinal.{u}) (j : blockIndex M K i) :
    (blockFunctor M K i).obj j ⟶ target M K :=
  (blockFunctor M K i).map (homOfLE le_top) ≫ afterRound M K i (WithTop.coe_lt_top i)

def blockStage (i : RoundOrdinal.{u}) (j : blockIndex M K i) :
    ConservativeMonoids.Subobject (forgetMargins.obj (target M K)) :=
  ConservativeMonoids.Subobject.range (forgetMargins.map (blockMap M K i j))

def outerStage (i : OuterIndex.{u}) :
    ConservativeMonoids.Subobject (forgetMargins.obj (target M K)) :=
  ConservativeMonoids.Subobject.range (forgetMargins.map (fromStage M K i))

theorem blockMap_naturality (i : RoundOrdinal.{u}) {j k : blockIndex M K i} (hjk : j ≤ k) :
    (blockFunctor M K i).map (homOfLE hjk) ≫ blockMap M K i k = blockMap M K i j := by
  unfold blockMap
  erw [← Category.assoc,← Functor.map_comp,homOfLE_comp]

theorem outerMap_naturality {i j : OuterIndex.{u}} (hij : i ≤ j) :
    (tower M K).map (homOfLE hij) ≫ fromStage M K j = fromStage M K i := by
  unfold fromStage
  erw [← Functor.map_comp,homOfLE_comp]

theorem blockStage_base (i : RoundOrdinal.{u}) : blockStage M K i ⊥ = outerStage M K i := by
  let b := blockBase M K i
  let sch := CompleteRound.schedule b K
  have he : Round.fromBase b sch ⊥ ≫ blockMap M K i ⊥ = fromStage M K i := by
    unfold blockMap
    erw [← Category.assoc,Round.fromBase_naturality]
    exact inclusion_afterRound M K i (WithTop.coe_lt_top i)
  have hf : Function.Surjective (forgetMargins.map (Round.fromBase b sch ⊥)) := by
    rw [← Round.bot_inv]
    exact (isoEquiv (Round.botIso b sch).symm).surjective
  have hh := ConservativeMonoids.Hom.range_comp_of_surjective
    (forgetMargins.map (Round.fromBase b sch ⊥)) (forgetMargins.map (blockMap M K i ⊥)) hf
  change Subobject.range (forgetMargins.map (Round.fromBase b sch ⊥ ≫ blockMap M K i ⊥)) = _ at hh
  rw [he] at hh
  exact hh.symm

theorem blockStage_top (i : RoundOrdinal.{u}) :
    blockStage M K i ⊤ = outerStage M K (Order.succ (i : OuterIndex)) := by
  have hb : blockMap M K i ⊤ = afterRound M K i (WithTop.coe_lt_top i) := by
    apply Hom.ext
    intro x
    change afterRound M K i (WithTop.coe_lt_top i)
      ((blockFunctor M K i).map (homOfLE le_top) x) = afterRound M K i _ x
    have h : (blockFunctor M K i).map (homOfLE (show (⊤ : blockIndex M K i) ≤ ⊤ from le_rfl)) = 𝟙 _ :=
      (blockFunctor M K i).map_id ⊤
    rw [h]
    rfl
  unfold blockStage
  rw [hb]
  exact ConservativeMonoids.Hom.range_comp_of_surjective
    (forgetMargins.map (succIso M K i (WithTop.coe_lt_top i)).inv)
    (forgetMargins.map (fromStage M K (Order.succ (i : OuterIndex))))
    (isoEquiv (succIso M K i (WithTop.coe_lt_top i)).symm).surjective

theorem blockStage_mono (i : RoundOrdinal.{u}) :
    Monotone (fun j => (blockStage M K i j).submonoid) := by
  intro j k hjk x hx
  obtain ⟨y,rfl⟩ := hx
  refine ⟨(blockFunctor M K i).map (homOfLE hjk) y,?_⟩
  exact congrArg (fun f : (blockFunctor M K i).obj j ⟶ target M K => f y)
    (blockMap_naturality M K i hjk)

theorem outerStage_mono : Monotone (fun i => (outerStage M K i).submonoid) := by
  intro i j hij x hx
  obtain ⟨y,rfl⟩ := hx
  refine ⟨(tower M K).map (homOfLE hij) y,?_⟩
  exact congrArg (fun f : (tower M K).obj i ⟶ target M K => f y)
    (outerMap_naturality M K hij)

theorem blockStage_limit (i : RoundOrdinal.{u}) (j : blockIndex M K i)
    (hj : Order.IsSuccLimit j) (x : target M K) (hx : x ∈ (blockStage M K i j).submonoid) :
    ∃ k < j, x ∈ (blockStage M K i k).submonoid := by
  obtain ⟨y,rfl⟩ := hx
  obtain ⟨k,hkj,z,hz⟩ := ContinuousTower.exists_rep (blockFunctor M K i) hj y
  refine ⟨k,hkj,z,?_⟩
  rw [← hz]
  exact (congrArg (fun f : (blockFunctor M K i).obj k ⟶ target M K => f z)
    (blockMap_naturality M K i hkj.le)).symm

theorem outerStage_limit (j : OuterIndex.{u}) (hj : Order.IsSuccLimit j)
    (x : target M K) (hx : x ∈ (outerStage M K j).submonoid) :
    ∃ k < j, x ∈ (outerStage M K k).submonoid := by
  obtain ⟨y,rfl⟩ := hx
  obtain ⟨k,hkj,z,hz⟩ := ContinuousTower.exists_rep (tower M K) hj y
  refine ⟨k,hkj,z,?_⟩
  rw [← hz]
  exact (congrArg (fun f : (tower M K).obj k ⟶ target M K => f z)
    (outerMap_naturality M K hkj.le)).symm

theorem blockStage_step (i : RoundOrdinal.{u}) (j : blockIndex M K i) (hj : j < ⊤) :
    Nonempty (Attachment (blockStage M K i j) (blockStage M K i (Order.succ j))) := by
  let b := blockBase M K i
  let sch := CompleteRound.schedule b K
  let d := (sch j).map (Round.fromBase b sch j)
  let e := Round.succIso b sch j (not_isMax_iff_ne_top.mpr hj.ne)
  let g := e.inv ≫ blockMap M K i (Order.succ j)
  have hc : d.inclusion ≫ g = blockMap M K i j := by
    dsimp only [g,e,d]
    rw [← Category.assoc,← Round.map_succ]
    exact blockMap_naturality M K i (Order.le_succ j)
  have h := request_rangeAttachment d (forgetMargins.map (blockMap M K i j)) (forgetMargins.map g)
    (fun x => congrArg (fun f : (blockFunctor M K i).obj j ⟶ target M K => f x) hc)
  have hg : Subobject.range (forgetMargins.map g) = blockStage M K i (Order.succ j) :=
    ConservativeMonoids.Hom.range_comp_of_surjective (forgetMargins.map e.inv)
      (forgetMargins.map (blockMap M K i (Order.succ j))) (isoEquiv e.symm).surjective
  rw [hg] at h
  exact h

/-- The executed omega-one many saturation rounds form a literal block tower
inside the very same final monoid. -/
def blocks : BlockTower (I := RoundOrdinal.{u}) (J := blockIndex M K)
    (forgetMargins.obj (target M K)) where
  stage := blockStage M K
  inner_mono := blockStage_mono M K
  outer_mono := by
    intro i j hij
    change (blockStage M K i ⊥).submonoid ≤ (blockStage M K j ⊥).submonoid
    rw [blockStage_base,blockStage_base]
    exact outerStage_mono M K (WithTop.coe_le_coe.mpr hij)
  boundary := by
    intro i
    rw [blockStage_top,blockStage_base]
    have hs : Order.succ (i : OuterIndex) = ((Order.succ i : RoundOrdinal) : OuterIndex) :=
      Order.succ_eq_of_covBy (WithTop.coe_covBy_coe.mpr (Order.covBy_succ i))
    rw [hs]
  inner_limit := blockStage_limit M K
  outer_limit := by
    intro i hi x hx
    rw [blockStage_base] at hx
    obtain ⟨k,hki,hxk⟩ := outerStage_limit M K i hi.withTopCoe x hx
    obtain ⟨k,rfl⟩ := WithTop.ne_top_iff_exists.mp (ne_of_lt (hki.trans_le le_top))
    refine ⟨k,WithTop.coe_lt_coe.mp hki,?_⟩
    rw [blockStage_base]
    exact hxk
  covers := by
    intro x
    obtain ⟨k,hk,g,hg⟩ := countable_stage M K (fun _ : Unit => x)
    obtain ⟨k,rfl⟩ := WithTop.ne_top_iff_exists.mp hk.ne
    refine ⟨k,?_⟩
    rw [blockStage_base]
    exact ⟨g (),hg ()⟩
  step := blockStage_step M K

abbrev FlatIndex := BlockIndex.Index RoundOrdinal.{u} (blockIndex M K)
def cells : CellTower (forgetMargins.obj (target M K)) (FlatIndex M K) := (blocks M K).flatten

end Saturation
end
end PartitionConsistency.MonoidConstruction

end OAI
