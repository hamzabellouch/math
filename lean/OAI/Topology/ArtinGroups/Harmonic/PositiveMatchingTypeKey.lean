import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.PositiveDegreeSublevelFinite
import OAI.Topology.ArtinGroups.Harmonic.TopBlockMatchingKey
import OAI.Topology.ArtinGroups.Realizations.PositiveLiftedCell

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)
variable (z:M.Group) (hz:∀w,M.toCoxeterSystem.length w≤M.toCoxeterSystem.length z)

noncomputable def positiveMatchingTypeKey (a:PositiveLiftedCell M) : ℕ :=
  if h:positiveCellTop M a=1 then 0 else
    topBlockMatchingKey (firstPositiveDescent M z hz (positiveCellTop M a) h) a.2.val.toFinset

def PositiveGradientStep (a b:PositiveLiftedCell M) : Prop :=
  (positiveCellToLifted M b≤positiveCellToLifted M a ∧ positiveCellTop M b≠positiveCellTop M a) ∨
  ∃h:positiveCellTop M a≠1,positiveCellTop M b=positiveCellTop M a ∧
    TopBlockStep (firstPositiveDescent M z hz (positiveCellTop M a) h)
      a.2.val.toFinset b.2.val.toFinset

theorem positiveGradient_wellFounded (inj:Function.Injective (positiveToArtin M)) :
    WellFounded (fun b a:PositiveLiftedCell M=>PositiveGradientStep M z hz a b) := by
  let key:=fun a:PositiveLiftedCell M=>(positiveDegree M (positiveCellTop M a),positiveMatchingTypeKey M z hz a)
  apply (InvImage.wf key (wellFounded_lt.prod_lex wellFounded_lt)).mono
  intro b a h
  change Prod.Lex (·<·) (·<·) (key b) (key a)
  rw [Prod.lex_iff]
  rcases h with ⟨hface,hne⟩|⟨ha,he,hs⟩
  · exact Or.inl (positiveCellTop_degree_strict M inj b a hface hne)
  · have hb:positiveCellTop M b≠1:=fun h=>ha (he.symm.trans h)
    refine Or.inr ⟨congrArg (positiveDegree M) he,?_⟩
    change positiveMatchingTypeKey M z hz b<positiveMatchingTypeKey M z hz a
    simpa only [positiveMatchingTypeKey,dite_eq_right ha,dite_eq_right hb,he] using topBlockStep_key hs

omit [LinearOrder S] in
theorem positiveCellTop_sublevel_finite (n:ℕ) :
    {a:PositiveLiftedCell M | positiveDegree M (positiveCellTop M a)≤n}.Finite := by
  apply ((positive_degree_sublevel_finite M n).prod (Set.toFinite (Set.univ:Set (SphericalType M)))).subset
  intro a ha
  dsimp [positiveCellTop] at ha
  rw [positiveDegree_mul] at ha
  exact ⟨by change positiveDegree M a.1≤n;omega,Set.mem_univ _⟩

lemma positiveGradient_sameTop_incident
    (a b:PositiveLiftedCell M) (ha:positiveCellTop M a≠1)
    (he:positiveCellTop M b=positiveCellTop M a)
    (hs:TopBlockStep (firstPositiveDescent M z hz (positiveCellTop M a) ha)
      a.2.val.toFinset b.2.val.toFinset) :
    positiveCellToLifted M a≤positiveCellToLifted M b ∨
      positiveCellToLifted M b≤positiveCellToLifted M a := by
  have hcell:∀c:PositiveLiftedCell M,positiveCellToLifted M c=
      cellWithTop M (positiveToArtin M (positiveCellTop M c)) c.2:=by
    intro c
    rw [positiveCellTop_toArtin]
    exact (cellWithTop_topVertex M (positiveCellToLifted M c)).symm
  have hAB:(a.2.val⊆b.2.val) ∨ (b.2.val⊆a.2.val):=by
    rcases hs with ⟨_,hs⟩|⟨_,_,_,hs⟩
    · left
      intro s h
      have ht:s∈b.2.val.toFinset:=by rw [hs];exact Finset.mem_insert_of_mem (Set.mem_toFinset.mpr h)
      exact Set.mem_toFinset.mp ht
    · right
      intro s h
      have ht:s∈a.2.val.toFinset:=by rw [hs];exact Finset.mem_insert_of_mem (Set.mem_toFinset.mpr h)
      exact Set.mem_toFinset.mp ht
  rw [hcell a,hcell b,he]
  exact hAB.imp (cellWithTop_mono M _) (cellWithTop_mono M _)

end HarmonicArtin

end OAI
