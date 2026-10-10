import Mathlib
import OAI.SetTheory.PartitionConsistency.Construction.MonoidBase

namespace OAI

/-! ## Tower -/

namespace PartitionConsistency.MonoidConstruction
universe u
open DiagramOrder CategoryTheory CategoryTheory.Limits
noncomputable section

instance : Category Object.{u} where
  Hom := Hom
  id := Hom.id
  comp f g := g.comp f
  id_comp := by intros; apply Hom.ext; intro; rfl
  comp_id := by intros; apply Hom.ext; intro; rfl
  assoc := by intros; apply Hom.ext; intro; rfl

instance (M N : Object.{u}) : CoeFun (M ⟶ N) (fun _ => M → N) :=
  ⟨fun f => f.toMonoidHom⟩

namespace DirectedColimit
variable {J : Type u} [Preorder J] [IsDirectedOrder J] [Nonempty J]
  (F : J ⥤ Object.{u})

abbrev Carrier (i : J) : Type u := F.obj i

def transition (i j : J) (h : i ≤ j) : F.obj i →* F.obj j :=
  (F.map (homOfLE h)).toMonoidHom

instance : DirectedSystem (Carrier F) (transition F · · ·) where
  map_self i x := by change (F.map (homOfLE (le_refl i))) x = x; simp [homOfLE_refl, F.map_id]; rfl
  map_map i j k hkj hji x := by
    change (F.map (homOfLE hji)) ((F.map (homOfLE hkj)) x) = _
    have h := F.map_comp (homOfLE hkj) (homOfLE hji)
    exact congrArg (fun g : F.obj k ⟶ F.obj i => g x) h.symm

omit [IsDirectedOrder J] [Nonempty J] in
theorem conservative (i j : J) (h : i ≤ j) : Conservative (transition F i j h) :=
  (F.map (homOfLE h)).conservative

abbrev Limit := DirectLimit (Carrier F) (transition F)

def old (i : J) : F.obj i →* Limit F := ConservativeLimit.of (transition F) i

theorem old_map (i j : J) (h : i ≤ j) (x : F.obj i) :
    old F j (F.map (homOfLE h) x) = old F i x :=
  ConservativeLimit.of_map (transition F) i j h x

theorem old_e (i j : J) : old F i (F.obj i).e = old F j (F.obj j).e := by
  obtain ⟨k,hik,hjk⟩ := exists_ge_ge i j
  rw [← old_map F i k hik, ← old_map F j k hjk]
  exact congrArg (old F k) ((F.map (homOfLE hik)).map_e.trans (F.map (homOfLE hjk)).map_e.symm)

def margin : HeightCost (LeftDivOrder (Limit F)) :=
  ConservativeLimit.heightCost (transition F) (fun i => (F.obj i).margin)
    (fun _ _ h => (F.map (homOfLE h)).height)
    (fun _ _ h => (F.map (homOfLE h)).cost)
    (conservative F) (fun _ _ h => (F.map (homOfLE h)).supremum)

def object : Object.{u} where
  Carrier := Limit F
  monoid := inferInstance
  conical := inferInstance
  joins := ConservativeLimit.conditionalJoins (transition F) (conservative F) (fun i => (F.obj i).joins)
  margin := margin F
  e := old F (Classical.arbitrary J) (F.obj (Classical.arbitrary J)).e
  e_ne_one h := (F.obj (Classical.arbitrary J)).e_ne_one
    ((ConservativeLimit.of_conservative (transition F) (conservative F)
      (Classical.arbitrary J)).injective h)

def inclusion (i : J) : F.obj i ⟶ object F where
  toMonoidHom := old F i
  conservative := ConservativeLimit.of_conservative (transition F) (conservative F) i
  map_e := old_e F i _
  height _ := rfl
  cost _ := rfl
  supremum := ConservativeLimit.old_cost_supremum (transition F) (fun i => (F.obj i).margin)
    (fun _ _ h => (F.map (homOfLE h)).cost) (conservative F)
    (fun _ _ h => (F.map (homOfLE h)).supremum) i

def cocone : Cocone F where
  pt := object F
  ι := {
    app := inclusion F
    naturality := by
      intro i j f
      apply Hom.ext
      intro x
      exact old_map F i j (leOfHom f) x }

variable (C : Cocone F)

def liftFun : object F → C.pt :=
  DirectLimit.lift (transition F) (fun i => C.ι.app i)
    (fun i j h x => by
      have he := congrArg (fun f : F.obj i ⟶ C.pt => f x) (C.ι.naturality (homOfLE h))
      exact he.symm)

@[simp] theorem lift_old (i : J) (x : F.obj i) : liftFun F C (old F i x) = C.ι.app i x := rfl

def liftMonoidHom : object F →* C.pt where
  toFun := liftFun F C
  map_one' := by
    calc
      liftFun F C 1 = liftFun F C (old F (Classical.arbitrary J) 1) :=
        congrArg (liftFun F C) (map_one (old F (Classical.arbitrary J))).symm
      _ = 1 := (C.ι.app (Classical.arbitrary J)).map_one
  map_mul' x y := by
    obtain ⟨i,x,y,rfl,rfl⟩ := DirectLimit.exists_eq_mk₂ (transition F) x y
    calc
      liftFun F C (old F i x * old F i y) = liftFun F C (old F i (x * y)) :=
        congrArg (liftFun F C) ((old F i).map_mul x y).symm
      _ = liftFun F C (old F i x) * liftFun F C (old F i y) :=
        (C.ι.app i).map_mul x y

theorem lift_conservative : Conservative (liftMonoidHom F C) where
  injective := by
    intro x y
    obtain ⟨i,x,y,rfl,rfl⟩ := DirectLimit.exists_eq_mk₂ (transition F) x y
    intro h
    exact congrArg (old F i) ((C.ι.app i).conservative.injective h)
  factors := by
    intro x y z
    obtain ⟨i,x,y,rfl,rfl⟩ := DirectLimit.exists_eq_mk₂ (transition F) x y
    intro h
    obtain ⟨t,ht⟩ := (C.ι.app i).conservative.factors x y z h
    exact ⟨old F i t,ht⟩
  intersections := by
    intro x y j hj z
    obtain ⟨i,x,y,j,rfl,rfl,rfl⟩ := DirectLimit.exists_eq_mk₃ (transition F) x y j
    have hj' : ∀ t : F.obj i, x ∣ t ∧ y ∣ t ↔ j ∣ t := by
      intro t
      have h := hj (old F i t)
      change old F i x ∣ old F i t ∧ old F i y ∣ old F i t ↔ old F i j ∣ old F i t at h
      simpa only [old, ConservativeLimit.of_dvd_iff (transition F) (conservative F)] using h
    exact (C.ι.app i).conservative.intersections x y j hj' z
  common := by
    intro x y
    obtain ⟨i,x,y,rfl,rfl⟩ := DirectLimit.exists_eq_mk₂ (transition F) x y
    intro h
    obtain ⟨z,hx,hy⟩ := (C.ι.app i).conservative.common x y h
    exact ⟨old F i z,(old F i).map_dvd hx,(old F i).map_dvd hy⟩

def lift : object F ⟶ C.pt where
  toMonoidHom := liftMonoidHom F C
  conservative := lift_conservative F C
  map_e := (C.ι.app (Classical.arbitrary J)).map_e
  height x := by
    obtain ⟨i,x,rfl⟩ := DirectLimit.exists_eq_mk (transition F) x
    exact (C.ι.app i).height x
  cost x := by
    obtain ⟨i,x,rfl⟩ := DirectLimit.exists_eq_mk (transition F) x
    exact (C.ι.app i).cost x
  supremum x y := by
    obtain ⟨i,x,y,rfl,rfl⟩ := DirectLimit.exists_eq_mk₂ (transition F) x y
    exact ((C.ι.app i).supremum x y).trans ((inclusion F i).supremum x y).symm

def isColimit : IsColimit (cocone F) where
  desc C := lift F C
  fac C i := by apply Hom.ext; intro x; rfl
  uniq C m hm := by
    apply Hom.ext
    intro x
    obtain ⟨i,x,rfl⟩ := DirectLimit.exists_eq_mk (transition F) x
    exact congrArg (fun f : F.obj i ⟶ C.pt => f x) (hm i)

end DirectedColimit

instance {J : Type u} [Preorder J] [IsDirectedOrder J] [Nonempty J] :
    HasColimitsOfShape J Object.{u} where
  has_colimit F := ⟨⟨⟨DirectedColimit.cocone F, DirectedColimit.isColimit F⟩⟩⟩

end
end PartitionConsistency.MonoidConstruction


/-! ## Iteration -/

namespace PartitionConsistency.ConstructionIteration
open CategoryTheory CategoryTheory.Limits
noncomputable section
universe u v w u₂ v₂ w₂

section ProductColimits
variable {C : Type u} {D : Type u₂} [Category.{v} C] [Category.{v₂} D]
  {I : Type w} [Category.{w₂} I] (F : I ⥤ C × D)

def pairCocone (c : Cocone (F ⋙ CategoryTheory.Prod.fst C D))
    (d : Cocone (F ⋙ CategoryTheory.Prod.snd C D)) : Cocone F where
  pt := (c.pt, d.pt)
  ι := {
    app i := (c.ι.app i, d.ι.app i)
    naturality i j f := by
      apply Prod.ext
      · exact c.ι.naturality f
      · exact d.ι.naturality f }

def isColimitPair {c : Cocone (F ⋙ CategoryTheory.Prod.fst C D)}
    {d : Cocone (F ⋙ CategoryTheory.Prod.snd C D)} (hc : IsColimit c) (hd : IsColimit d) :
    IsColimit (pairCocone F c d) where
  desc s := (hc.desc ((CategoryTheory.Prod.fst C D).mapCocone s),
    hd.desc ((CategoryTheory.Prod.snd C D).mapCocone s))
  fac _ i := Prod.ext (hc.fac _ i) (hd.fac _ i)
  uniq s m hm := Prod.ext (hc.uniq ((CategoryTheory.Prod.fst C D).mapCocone s) m.1 (fun i => congrArg Prod.fst (hm i)))
    (hd.uniq ((CategoryTheory.Prod.snd C D).mapCocone s) m.2 (fun i => congrArg Prod.snd (hm i)))

def isColimitFst {c : Cocone F} (hc : IsColimit c) :
    IsColimit ((CategoryTheory.Prod.fst C D).mapCocone c) where
  desc s := (hc.desc (pairCocone F s ((CategoryTheory.Prod.snd C D).mapCocone c))).1
  fac s i := congrArg Prod.fst (hc.fac _ i)
  uniq s m hm := by
    have h := hc.uniq (pairCocone F s ((CategoryTheory.Prod.snd C D).mapCocone c))
      (m, 𝟙 c.pt.2) (fun i => Prod.ext (hm i) (Category.comp_id _))
    exact congrArg Prod.fst h

def isColimitSnd {c : Cocone F} (hc : IsColimit c) :
    IsColimit ((CategoryTheory.Prod.snd C D).mapCocone c) where
  desc s := (hc.desc (pairCocone F ((CategoryTheory.Prod.fst C D).mapCocone c) s)).2
  fac s i := congrArg Prod.snd (hc.fac _ i)
  uniq s m hm := by
    have h := hc.uniq (pairCocone F ((CategoryTheory.Prod.fst C D).mapCocone c) s)
      (𝟙 c.pt.1, m) (fun i => Prod.ext (Category.comp_id _) (hm i))
    exact congrArg Prod.snd h

instance [HasColimitsOfShape I C] [HasColimitsOfShape I D] :
    HasColimitsOfShape I (C × D) where
  has_colimit F := ⟨⟨⟨pairCocone F (colimit.cocone _) (colimit.cocone _),
    isColimitPair F (colimit.isColimit _) (colimit.isColimit _)⟩⟩⟩

instance : PreservesColimitsOfShape I (CategoryTheory.Prod.fst C D) where
  preservesColimit := { preserves hc := ⟨isColimitFst _ hc⟩ }

instance : PreservesColimitsOfShape I (CategoryTheory.Prod.snd C D) where
  preservesColimit := { preserves hc := ⟨isColimitSnd _ hc⟩ }

end ProductColimits


/-- Stage-indexed iteration. The second factor records the actual stage;
limits take its supremum, rather than skipping pending operations. -/
structure Step {C : Type u} [Category.{v} C] (X : C) where
  target : C
  map : X ⟶ target

variable {C : Type u} [Category.{v} C]
  {J : Type w} [CompleteLinearOrder J] [SuccOrder J] [WellFoundedLT J]
  [HasIterationOfShape J C]

instance : HasIterationOfShape J (C × J) where
  hasColimitsOfShape_of_isSuccLimit j hj := by
    have := hasColimitsOfShape_of_isSuccLimit C j hj
    infer_instance

instance : PreservesWellOrderContinuousOfShape J (CategoryTheory.Prod.fst C J) where
instance : PreservesWellOrderContinuousOfShape J (CategoryTheory.Prod.snd C J) where

variable (X₀ : C) (next : J → (X : C) → Step X)

def structureWithTime : CategoryTheory.SmallObject.SuccStruct (C × J) where
  X₀ := (X₀, ⊥)
  succ X := ((next X.2 X.1).target, Order.succ X.2)
  toSucc X := ((next X.2 X.1).map, homOfLE (Order.le_succ X.2))

abbrev fullFunctor : J ⥤ C × J := (structureWithTime X₀ next).iterationFunctor J
abbrev functor : J ⥤ C := fullFunctor X₀ next ⋙ CategoryTheory.Prod.fst C J
abbrev timeFunctor : J ⥤ J := fullFunctor X₀ next ⋙ CategoryTheory.Prod.snd C J

theorem time (j : J) : ((fullFunctor X₀ next).obj j).2 = j := by
  induction j using SuccOrder.limitRecOn with
  | isMin j hj =>
    obtain rfl : j = ⊥ := by simpa using hj
    exact ((CategoryTheory.Prod.snd C J).mapIso
      ((structureWithTime X₀ next).iterationFunctorObjBotIso J)).to_eq
  | succ j hj ih =>
    have h := ((CategoryTheory.Prod.snd C J).mapIso
      ((structureWithTime X₀ next).iterationFunctorObjSuccIso j hj)).to_eq
    exact h.trans (congrArg Order.succ ih)
  | isSuccLimit j hj ih =>
    have hc := (timeFunctor X₀ next).isColimitOfIsWellOrderContinuous j hj
    have hl := Preorder.isLUB_of_isColimit _ hc
    have hr : Set.range (((Set.principalSegIio j).monotone.functor ⋙
        timeFunctor X₀ next).obj) = Set.Iio j := by
      ext k
      constructor
      · rintro ⟨⟨i,hi⟩,rfl⟩
        change ((fullFunctor X₀ next).obj i).2 < j
        rw [ih i hi]
        exact hi
      · intro hk
        exact ⟨⟨k,hk⟩, ih k hk⟩
    rw [hr] at hl
    exact hl.unique hj.isLUB_Iio

def botIso : (functor X₀ next).obj ⊥ ≅ X₀ :=
  (CategoryTheory.Prod.fst C J).mapIso ((structureWithTime X₀ next).iterationFunctorObjBotIso J)

def succIso (j : J) (hj : ¬IsMax j) :
    (functor X₀ next).obj (Order.succ j) ≅ (next j ((functor X₀ next).obj j)).target :=
  (CategoryTheory.Prod.fst C J).mapIso ((structureWithTime X₀ next).iterationFunctorObjSuccIso j hj) ≪≫
    eqToIso (congrArg (fun i => (next i ((functor X₀ next).obj j)).target) (time X₀ next j))

theorem map_succ (j : J) (hj : ¬IsMax j) :
    (functor X₀ next).map (homOfLE (Order.le_succ j)) =
      (next j ((functor X₀ next).obj j)).map ≫ (succIso X₀ next j hj).inv := by
  have h := congrArg ((CategoryTheory.Prod.fst C J).map)
    ((structureWithTime X₀ next).iterationFunctor_map_succ j hj)
  dsimp only [Functor.comp_map, functor]
  rw [h]
  dsimp [succIso]
  have hn (i k : J) (h : i = k) (X : C) :
      (next i X).map = (next k X).map ≫
        (eqToIso (congrArg (fun i => (next i X).target) h)).inv := by
    cases h
    simp
  change (next ((fullFunctor X₀ next).obj j).2 ((fullFunctor X₀ next).obj j).1).map ≫ _ = _
  rw [hn _ _ (time X₀ next j)]
  exact Category.assoc _ _ _


end
end PartitionConsistency.ConstructionIteration

namespace PartitionConsistency.MonoidConstruction
open CategoryTheory CategoryTheory.Limits
universe u

instance {J : Type u} [LinearOrder J] [Nonempty J] : HasIterationOfShape J Object.{u} where
  hasColimitsOfShape_of_isSuccLimit j hj := by
    have := hj.nonempty_Iio.to_subtype
    infer_instance

end PartitionConsistency.MonoidConstruction

end OAI
