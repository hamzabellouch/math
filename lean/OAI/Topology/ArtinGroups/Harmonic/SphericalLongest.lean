import Mathlib
import OAI.Topology.ArtinGroups.Realizations.WeightInclusion
import OAI.Topology.ArtinGroups.Cancellation.SphericalPositiveCancelMonoid
import OAI.Topology.ArtinGroups.Harmonic.PositiveDescentSet
import OAI.Topology.ArtinGroups.Harmonic.LiftedDeck

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric
open scoped unitInterval

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] (M:CoxeterMatrix S)

lemma parabolic_longest_unique (T:Set S) (q r:M.Group)
    (hq:IsParabolicLongest M T q) (hr:IsParabolicLongest M T r) : q=r := by
  have hh:=parabolic_longest_length_mul M T q hq r⁻¹ ((coxeterParabolic M T).inv_mem hr.1)
  rw [M.toCoxeterSystem.length_inv] at hh
  have hb:=hr.2 q hq.1
  have he:q*r⁻¹=1:=M.toCoxeterSystem.length_eq_zero_iff.mp (by omega)
  exact mul_inv_eq_one.mp he

noncomputable def sphericalLongest (T:SphericalType M) : M.Group :=
  (exists_parabolic_longest M T.val T.property).choose

lemma sphericalLongest_spec (T:SphericalType M) :
    IsParabolicLongest M T.val (sphericalLongest M T) :=
  (exists_parabolic_longest M T.val T.property).choose_spec

omit [Fintype S] in
lemma positiveToArtin_simpleLift (w:M.Group) :
    positiveToArtin M (positiveSimpleLift M w)=positiveLift M w := by
  simp only [positiveSimpleLift,positiveToArtin_word,positiveLift]

noncomputable def liftedTopVertex (a:LiftedCell M) : Artin M :=
  a.1*positiveLift M (sphericalLongest M a.2)

noncomputable def cellWithTop (b:Artin M) (T:SphericalType M) : LiftedCell M :=
  (b*(positiveLift M (sphericalLongest M T))⁻¹,T)

lemma cellWithTop_top (b:Artin M) (T:SphericalType M) :
    liftedTopVertex M (cellWithTop M b T)=b := by
  simp only [liftedTopVertex,cellWithTop,mul_assoc,inv_mul_cancel,mul_one]

lemma cellWithTop_topVertex (a:LiftedCell M) :
    cellWithTop M (liftedTopVertex M a) a.2=a := by
  obtain ⟨g,T⟩:=a
  simp only [cellWithTop,liftedTopVertex,mul_inv_cancel_right]

lemma cellWithTop_mono (b:Artin M) {R T:SphericalType M} (hle:R.val⊆T.val) :
    cellWithTop M b R≤cellWithTop M b T :=
  lifted_same_top_le M R.val T.val R.property T.property hle _ _
    (sphericalLongest_spec M R) (sphericalLongest_spec M T) b

abbrev PositiveTopBlock (b:PositiveArtin M) :=
  {a:LiftedCell M // (∃p:PositiveArtin M,a.1=positiveToArtin M p) ∧
    liftedTopVertex M a=positiveToArtin M b}

instance (b:PositiveArtin M) : PartialOrder (PositiveTopBlock M b) := inferInstanceAs
  (PartialOrder {a:LiftedCell M // (∃p:PositiveArtin M,a.1=positiveToArtin M p) ∧
    liftedTopVertex M a=positiveToArtin M b})

theorem positiveTopBlock_has_greatest
    (z:M.Group) (hz:∀w,M.toCoxeterSystem.length w≤M.toCoxeterSystem.length z)
    (inj:Function.Injective (positiveToArtin M)) (b:PositiveArtin M) :
    ∃c:PositiveTopBlock M b,∀a:PositiveTopBlock M b,a≤c := by
  have cancel:∀a d e:PositiveArtin M,a*d=a*e→d=e:=by
    intro a d e h
    apply inj
    exact mul_left_cancel (by simpa only [map_mul] using congrArg (positiveToArtin M) h)
  obtain ⟨hs,q,hq,hdiv⟩:=positive_descent_fundamental M z hz cancel b
  let D:SphericalType M:=⟨PositiveDescentSet M b,hs⟩
  have he:sphericalLongest M D=q:=parabolic_longest_unique M D.val _ _ (sphericalLongest_spec M D) hq
  obtain ⟨p,hp⟩:=hdiv
  have hb:b=p*positiveSimpleLift M q:=hp
  have hpos:(cellWithTop M (positiveToArtin M b) D).1=positiveToArtin M p:=by
    change positiveToArtin M b*(positiveLift M (sphericalLongest M D))⁻¹=_
    rw [he,hb,map_mul,positiveToArtin_simpleLift,mul_inv_cancel_right]
  let c:PositiveTopBlock M b:=⟨cellWithTop M (positiveToArtin M b) D,
    ⟨p,hpos⟩,cellWithTop_top M _ _⟩
  refine ⟨c,?_⟩
  intro a
  obtain ⟨r,hr⟩:=a.property.1
  have hfactor:b=r*positiveSimpleLift M (sphericalLongest M a.val.2):=by
    apply inj
    rw [map_mul,positiveToArtin_simpleLift]
    exact (show a.val.1*positiveLift M (sphericalLongest M a.val.2)=positiveToArtin M b from a.property.2).symm.trans
      (by rw [hr])
  have hsub:a.val.2.val⊆D.val:=by
    change a.val.2.val⊆PositiveDescentSet M b
    simpa only [←hfactor] using type_subset_positiveDescentSet M _ _ (sphericalLongest_spec M a.val.2) r
  change a.val≤cellWithTop M (positiveToArtin M b) D
  have ha:a.val=cellWithTop M (positiveToArtin M b) a.val.2:=by
    exact (cellWithTop_topVertex M a.val).symm.trans
      (congrArg (fun g=>cellWithTop M g a.val.2) a.property.2)
  rw [ha]
  exact cellWithTop_mono M _ hsub

theorem positiveTopBlock_contractible
    (z:M.Group) (hz:∀w,M.toCoxeterSystem.length w≤M.toCoxeterSystem.length z)
    (inj:Function.Injective (positiveToArtin M)) (b:PositiveArtin M) :
    ContractibleSpace (OrderWeights (PositiveTopBlock M b)) := by
  obtain ⟨c,hc⟩:=positiveTopBlock_has_greatest M z hz inj b
  let H:(ContinuousMap.id (OrderWeights (PositiveTopBlock M b))).Homotopy
      (ContinuousMap.const _ (weightVertex c)):={
    toFun p:=coneWeights OrderHom.id c (fun a=>Or.inl (hc a)) p.1 p.2
    continuous_toFun:=coneWeights_continuous _ _ _
    map_zero_left:=fun w=>by rw [coneWeights_zero,weightMap_id];rfl
    map_one_left:=fun w=>coneWeights_one_vertex _ _ _ w }
  exact (contractible_iff_id_nullhomotopic _).mpr ⟨weightVertex c,⟨H⟩⟩

theorem spherical_positiveTopBlock_contractible {A:Type} [Fintype A] [LinearOrder A]
    (N:CoxeterMatrix A) (T:Set A) (hT:IsSpherical N T)
    (b:PositiveArtin (restrictedMatrix N T)) :
    ContractibleSpace (OrderWeights (PositiveTopBlock (restrictedMatrix N T) b)) := by
  have : Finite (restrictedMatrix N T).Group := restricted_finite N T hT
  obtain ⟨z,hz⟩:=exists_longest (restrictedMatrix N T).toCoxeterSystem
  exact positiveTopBlock_contractible (restrictedMatrix N T) z hz
    (spherical_positiveToArtin_injective N T hT) b

end HarmonicArtin

end OAI
