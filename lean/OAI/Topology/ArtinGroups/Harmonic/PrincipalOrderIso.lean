import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.LiftedDeckOrderHom
import OAI.Topology.ArtinGroups.Realizations.WeightUpperCone
import OAI.Topology.ArtinGroups.Coxeter.AmbientCoxeterFace

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric Topology

attribute [local instance] Classical.decEq Classical.propDecidable

def principalOrderIso {P Q : Type*} [PartialOrder P] [PartialOrder Q] (e : P ≃o Q) (a : P) :
    Set.Iic a ≃o Set.Iic (e a) where
  toFun x := ⟨e x,e.monotone x.property⟩
  invFun y := ⟨e.symm y,e.symm_apply_le.mpr y.property⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv y := Subtype.ext (e.apply_symm_apply y)
  map_rel_iff' := e.le_iff_le

variable {S : Type*} [Fintype S] [DecidableEq S] (M : CoxeterMatrix S)

instance sourceRestrictionFinite (T : SphericalType M) : Finite (restrictedMatrix M T.val).Group :=
  restricted_finite M T.val T.property

abbrev SourceModelCell (T : SphericalType M) := permutahedron (restrictedMatrix M T.val)

noncomputable def sourceModelHomeomorph (T : SphericalType M) :
    SourceModelCell M T ≃ₜ OrderWeights (Set.Iic ((1,T) : LiftedCell M)) :=
  (permutahedronBarycentricHomeomorph (restrictedMatrix M T.val)).symm.trans
    (weightHomeomorph (sourceCellFaceIso M T))

omit [Fintype S] [DecidableEq S] in
lemma deck_source (a : LiftedCell M) : liftedDeck M a.1 (1,a.2)=a := by
  exact Prod.ext (mul_one _) rfl

noncomputable def sourcePrincipalDeck (a : LiftedCell M) :
    Set.Iic ((1,a.2) : LiftedCell M) ≃o Set.Iic a :=
  (principalOrderIso (liftedDeck M a.1) (1,a.2)).trans
    (Set.orderIsoOfEq _ _ (congrArg Set.Iic (deck_source M a)))

noncomputable def liftedModelHomeomorph (a : LiftedCell M) :
    SourceModelCell M a.2 ≃ₜ OrderWeights (Set.Iic a) :=
  (sourceModelHomeomorph M a.2).trans (weightHomeomorph (sourcePrincipalDeck M a))

noncomputable def sourceCellMap (a : LiftedCell M) : C(SourceModelCell M a.2,OrderWeights (LiftedCell M)) :=
  (weightMapContinuous (weightInclusion (Set.Iic a))).comp ⟨liftedModelHomeomorph M a,(liftedModelHomeomorph M a).continuous⟩

lemma sourceCellMap_injective (a : LiftedCell M) : Function.Injective (sourceCellMap M a) :=
  (weightMap_injective _ Subtype.val_injective).comp (liftedModelHomeomorph M a).injective

lemma sourceCellMap_support (a : LiftedCell M) (x : SourceModelCell M a.2) :
    ∀ p ∈ (sourceCellMap M a x).weights.support,p ≤ a := by
  let : DecidableEq (LiftedCell M) := Classical.decEq _
  intro p hp
  change p ∈ (weightMap (weightInclusion (Set.Iic a)) ((liftedModelHomeomorph M a) x)).weights.support at hp
  rw [weightMap_support_embedding _ Subtype.val_injective] at hp
  obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hp
  exact q.property

lemma sourceCellMap_range (a : LiftedCell M) (w : OrderWeights (LiftedCell M))
    (hw : ∀ p ∈ w.weights.support,p ≤ a) : ∃ x,sourceCellMap M a x=w := by
  refine ⟨(liftedModelHomeomorph M a).symm (weightRestrict (Set.Iic a) w hw),?_⟩
  change weightMap _ ((liftedModelHomeomorph M a) ((liftedModelHomeomorph M a).symm _))=w
  rw [Homeomorph.apply_symm_apply]
  exact weightRestrict_map _ w hw

noncomputable def sourceModelFaceMap {a b : LiftedCell M} (h : a ≤ b) :
    C(SourceModelCell M a.2,SourceModelCell M b.2) :=
  (ContinuousMap.mk (liftedModelHomeomorph M b).symm (liftedModelHomeomorph M b).symm.continuous).comp
    ((weightMapContinuous (weightSubset (Set.Iic a) (Set.Iic b) (fun _ hx => hx.trans h))).comp
      ⟨liftedModelHomeomorph M a,(liftedModelHomeomorph M a).continuous⟩)

lemma sourceModelFaceMap_included {a b : LiftedCell M} (h : a ≤ b) (x : SourceModelCell M a.2) :
    sourceCellMap M b (sourceModelFaceMap M h x)=sourceCellMap M a x := by
  change weightMap _ ((liftedModelHomeomorph M b) ((liftedModelHomeomorph M b).symm _))=_
  rw [Homeomorph.apply_symm_apply]
  change weightMap (weightInclusion (Set.Iic b))
    (weightMap (weightSubset (Set.Iic a) (Set.Iic b) (fun _ hx => hx.trans h))
      ((liftedModelHomeomorph M a) x)) = weightMap (weightInclusion (Set.Iic a)) _
  exact weightMap_comp _ _ _

lemma sourceModelFaceMap_self (a : LiftedCell M) (x : SourceModelCell M a.2) :
    sourceModelFaceMap M (le_refl a) x=x := by
  apply sourceCellMap_injective M a
  exact sourceModelFaceMap_included M _ x

lemma sourceModelFaceMap_comp {a b c : LiftedCell M} (hab : a ≤ b) (hbc : b ≤ c)
    (x : SourceModelCell M a.2) :
    sourceModelFaceMap M hbc (sourceModelFaceMap M hab x)=sourceModelFaceMap M (hab.trans hbc) x := by
  apply sourceCellMap_injective M c
  rw [sourceModelFaceMap_included,sourceModelFaceMap_included,sourceModelFaceMap_included]

lemma sourceCellMap_deck (g : Artin M) (a : LiftedCell M) (x : SourceModelCell M a.2) :
    sourceCellMap M (liftedDeck M g a) x=g • sourceCellMap M a x := by
  change sourceCellMap M (g*a.1,a.2) x=g • sourceCellMap M a x
  let f : Set.Iic ((1,a.2) : LiftedCell M) →o LiftedCell M :=
    (weightInclusion (Set.Iic a)).comp (sourcePrincipalDeck M a : Set.Iic ((1,a.2) : LiftedCell M) →o Set.Iic a)
  let f' : Set.Iic ((1,a.2) : LiftedCell M) →o LiftedCell M :=
    (weightInclusion (Set.Iic ((g*a.1,a.2) : LiftedCell M))).comp
      (sourcePrincipalDeck M (g*a.1,a.2) : Set.Iic ((1,a.2) : LiftedCell M) →o Set.Iic ((g*a.1,a.2) : LiftedCell M))
  have hf : f'=(liftedDeckOrderHom M g).comp f := by
    apply OrderHom.ext
    funext p
    exact Prod.ext (mul_assoc g a.1 p.val.1) rfl
  have ha : sourceCellMap M a x=weightMap f ((sourceModelHomeomorph M a.2) x) :=
    weightMap_comp _ _ _
  have hb : sourceCellMap M (g*a.1,a.2) x=weightMap f' ((sourceModelHomeomorph M a.2) x) :=
    weightMap_comp _ _ _
  rw [ha,hb,hf]
  exact (weightMap_comp _ _ _).symm

lemma sourceModelFaceMap_deck (g : Artin M) {a b : LiftedCell M} (h : a ≤ b)
    (x : SourceModelCell M a.2) : sourceModelFaceMap M ((liftedDeck M g).monotone h) x=
      sourceModelFaceMap M h x := by
  have h' : (g*a.1,a.2) ≤ (g*b.1,b.2) := (liftedDeck M g).monotone h
  change sourceModelFaceMap M h' x=sourceModelFaceMap M h x
  apply sourceCellMap_injective M (g*b.1,b.2)
  calc
    _ = sourceCellMap M (g*a.1,a.2) x :=
      sourceModelFaceMap_included M (a := (g*a.1,a.2)) (b := (g*b.1,b.2)) h' x
    _ = g • sourceCellMap M a x := sourceCellMap_deck M g a x
    _ = g • sourceCellMap M b (sourceModelFaceMap M h x) :=
      congrArg (g • ·) (sourceModelFaceMap_included M h x).symm
    _ = _ := (sourceCellMap_deck M g b _).symm

end HarmonicArtin

end OAI
