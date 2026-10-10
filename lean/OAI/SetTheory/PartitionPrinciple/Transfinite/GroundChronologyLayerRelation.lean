import OAI.SetTheory.PartitionPrinciple.Geometry.GroundGrowthLayerRecognition
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundSerializedChronologyTimeEquality

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace BoundedFormula

def chronologyLayerPairLookupFormula {n} (p T Qs rs μs births : Fin n)
    (v : Fin 6 → Fin n) : BoundedFormula n :=
  .conj (.mem (v 0) T) (.conj (.mem (v 1) T)
    (.conj (disj (.equal (v 1) (v 0)) (.mem (v 1) (v 0)))
      (.conj (orderedPairFormula p (v 0) (v 1))
        (.conj (pairMembershipFormula (v 0) (v 2) Qs)
          (.conj (pairMembershipFormula (v 0) (v 3) rs)
            (.conj (pairMembershipFormula (v 0) (v 4) μs)
              (pairMembershipFormula (v 0) (v 5) births)))))))

theorem truth_chronologyLayerPairLookupFormula {n} (p T Qs rs μs births : Fin n)
    (v : Fin 6 → Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (chronologyLayerPairLookupFormula p T Qs rs μs births v) env ↔
      env (v 0) ∈ env T ∧ env (v 1) ∈ env T ∧
      (env (v 1) = env (v 0) ∨ env (v 1) ∈ env (v 0)) ∧
      env p = ZFSet.pair (env (v 0)) (env (v 1)) ∧
      ZFSet.pair (env (v 0)) (env (v 2)) ∈ env Qs ∧
      ZFSet.pair (env (v 0)) (env (v 3)) ∈ env rs ∧
      ZFSet.pair (env (v 0)) (env (v 4)) ∈ env μs ∧
      ZFSet.pair (env (v 0)) (env (v 5)) ∈ env births := by
  simp only [chronologyLayerPairLookupFormula, Truth, truth_disj,
    truth_orderedPairFormula, truth_pairMembershipFormula]
end BoundedFormula

namespace SetFormula

def chronologyLayerRelationFormula : SetFormula 8 :=
  let old := suffixIndex 8 6
  let v := prefixIndex 8 6
  exBlock 6 (.conj
    (BoundedFormula.chronologyLayerPairLookupFormula (old 0) (old 2) (old 3) (old 4) (old 5) (old 6) v).toFormula
    (growthLayerWitnessFormula (old 1) (old 3) (old 4) (old 5) (v 2) (v 3) (v 4) (v 5) (v 1) (old 7)))
end SetFormula

namespace GroundChronologyFields
variable {M : TransitiveGround.{u}} {T C D rD : ZFSet.{u}}
variable (fields : GroundChronologyFields M T)

noncomputable def layerRelationParams (N : ZFSet.{u}) : Fin 6 → ZFSet.{u} :=
  Fin.cases T (Fin.cases (fields.graph 0) (Fin.cases (fields.graph 1)
    (Fin.cases (fields.graph 2) (Fin.cases (fields.graph 3) (fun _ => N)))))

theorem layerRelationParams_ground {N : ZFSet.{u}} (hN : N ∈ M.sets) :
    ∀ i, fields.layerRelationParams N i ∈ M.sets :=
  Fin.cases fields.time_ground (Fin.cases (fields.graph_ground 0) (Fin.cases (fields.graph_ground 1)
    (Fin.cases (fields.graph_ground 2) (Fin.cases (fields.graph_ground 3) (fun _ => hN)))))

theorem realize_chronologyLayerRelation
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (core : ChronologyCoreCode T fields.bound C D rD fields.graph)
    {N z s t : ZFSet.{u}} (hN : N ∈ M.sets) (hz : z ∈ M.sets)
    (hs : s ∈ T) (ht : t ∈ T) (earlier : t = s ∨ t ∈ s) :
    Realize M.sets chronologyLayerRelationFormula
      (extend (ZFSet.pair s t) (extend z (fields.layerRelationParams N))) ↔
      GrowthLayerWitnessCode (fields.graph 0) (fields.graph 1) (fields.graph 2)
        (fields.value 0 s) (fields.value 1 s) (fields.value 2 s) (fields.value 3 s) t N z := by
  let env := extend (ZFSet.pair s t) (extend z (fields.layerRelationParams N))
  have members : ∀ i, env i ∈ M.sets := Fin.cases
    (M.orderedPair_mem pairing (M.transitive fields.time_ground hs) (M.transitive fields.time_ground ht))
    (Fin.cases hz (fields.layerRelationParams_ground hN))
  rw [chronologyLayerRelationFormula, realize_exBlock]
  constructor
  · rintro ⟨v, ground, recognized⟩
    have allGround := extendMany_members 6 v env ground members
    have lookup := (BoundedFormula.truth_chronologyLayerPairLookupFormula
      (suffixIndex 8 6 0) (suffixIndex 8 6 2) (suffixIndex 8 6 3) (suffixIndex 8 6 4)
      (suffixIndex 8 6 5) (suffixIndex 8 6 6) (prefixIndex 8 6) (extendMany 6 v env)).1
        ((BoundedFormula.realize_toFormula M _ _ allGround).1 recognized.1)
    simp only [extendMany_prefix, extendMany_suffix] at lookup
    change v 0 ∈ T ∧ v 1 ∈ T ∧ (v 1 = v 0 ∨ v 1 ∈ v 0) ∧
      ZFSet.pair s t = ZFSet.pair (v 0) (v 1) ∧
      ZFSet.pair (v 0) (v 2) ∈ fields.graph 0 ∧
      ZFSet.pair (v 0) (v 3) ∈ fields.graph 1 ∧
      ZFSet.pair (v 0) (v 4) ∈ fields.graph 2 ∧
      ZFSet.pair (v 0) (v 5) ∈ fields.graph 3 at lookup
    have same := ZFSet.pair_inj.1 lookup.2.2.2.1
    have eL := fields.value_eq_of_entry 0 lookup.2.2.2.2.1
    have er := fields.value_eq_of_entry 1 lookup.2.2.2.2.2.1
    have eμ := fields.value_eq_of_entry 2 lookup.2.2.2.2.2.2.1
    have eb := fields.value_eq_of_entry 3 lookup.2.2.2.2.2.2.2
    have meet : MeetOrderCode (v 2) (v 3) (v 4) :=
      eL ▸ er ▸ eμ ▸ (fields.decoded_point core lookup.1).meet
    have liftedMeet : MeetOrderCode
        (extendMany 6 v env (prefixIndex 8 6 2)) (extendMany 6 v env (prefixIndex 8 6 3))
        (extendMany 6 v env (prefixIndex 8 6 4)) := by
      simpa only [extendMany_prefix] using meet
    have witness := (M.realize_growthLayerWitnessFormula unions (suffixIndex 8 6 1)
      (suffixIndex 8 6 3) (suffixIndex 8 6 4) (suffixIndex 8 6 5)
      (prefixIndex 8 6 2) (prefixIndex 8 6 3) (prefixIndex 8 6 4) (prefixIndex 8 6 5)
      (prefixIndex 8 6 1) (suffixIndex 8 6 7) (extendMany 6 v env) allGround liftedMeet).1 recognized.2
    simp only [extendMany_prefix, extendMany_suffix] at witness
    change GrowthLayerWitnessCode _ _ _ (v 2) (v 3) (v 4) (v 5) (v 1) N z at witness
    rw [← eL, ← er, ← eμ, ← eb, ← same.1, ← same.2] at witness
    exact witness
  · intro witness
    let v : Fin 6 → ZFSet.{u} := Fin.cases s (Fin.cases t (Fin.cases (fields.value 0 s)
      (Fin.cases (fields.value 1 s) (Fin.cases (fields.value 2 s) (fun _ => fields.value 3 s)))))
    have ground : ∀ i, v i ∈ M.sets := Fin.cases (M.transitive fields.time_ground hs)
      (Fin.cases (M.transitive fields.time_ground ht) (Fin.cases (fields.value_ground 0 s)
        (Fin.cases (fields.value_ground 1 s) (Fin.cases (fields.value_ground 2 s) (fun _ => fields.value_ground 3 s)))))
    have allGround := extendMany_members 6 v env ground members
    refine ⟨v, ground, ?_, ?_⟩
    · apply (BoundedFormula.realize_toFormula M _ _ allGround).2
      apply (BoundedFormula.truth_chronologyLayerPairLookupFormula
        (suffixIndex 8 6 0) (suffixIndex 8 6 2) (suffixIndex 8 6 3) (suffixIndex 8 6 4)
        (suffixIndex 8 6 5) (suffixIndex 8 6 6) (prefixIndex 8 6) (extendMany 6 v env)).2
      simp only [extendMany_prefix, extendMany_suffix]
      exact ⟨hs, ht, earlier, rfl, fields.value_entry 0 hs, fields.value_entry 1 hs,
        fields.value_entry 2 hs, fields.value_entry 3 hs⟩
    · have liftedMeet : MeetOrderCode
          (extendMany 6 v env (prefixIndex 8 6 2)) (extendMany 6 v env (prefixIndex 8 6 3))
          (extendMany 6 v env (prefixIndex 8 6 4)) := by
        simp only [extendMany_prefix]
        exact (fields.decoded_point core hs).meet
      apply (M.realize_growthLayerWitnessFormula unions (suffixIndex 8 6 1)
        (suffixIndex 8 6 3) (suffixIndex 8 6 4) (suffixIndex 8 6 5)
        (prefixIndex 8 6 2) (prefixIndex 8 6 3) (prefixIndex 8 6 4) (prefixIndex 8 6 5)
        (prefixIndex 8 6 1) (suffixIndex 8 6 7) (extendMany 6 v env) allGround liftedMeet).2
      simp only [extendMany_prefix, extendMany_suffix]
      exact witness

end GroundChronologyFields

end PartitionPilot.Forcing

end

end OAI
