import Mathlib
import OAI.Topology.ArtinGroups.Realizations.RestrictedCellEmbedding
import OAI.Topology.ArtinGroups.Realizations.PositiveFullCell

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)
variable (z : M.Group) (hz : ∀ w, M.toCoxeterSystem.length w ≤ M.toCoxeterSystem.length z)
variable (inj : Function.Injective (positiveToArtin M))

lemma matchingLetter_le_type (a : NoncriticalPositiveCell M) (t : S) (ht : t ∈ a.val.2.val) :
    matchingLetter M z hz a ≤ t :=
  firstPositiveDescent_le M z hz _ _
    (type_subset_positiveDescentSet M _ _ (sphericalLongest_spec M a.val.2) a.val.1 ht)

variable (a : NoncriticalPositiveCell M) (hs : matchingLetter M z hz a ∈ a.val.2.val)
variable [Finite (restrictedMatrix M a.val.2.val).Group]
variable (q : (restrictedMatrix M a.val.2.val).Group)
variable (hq : ∀ w, (restrictedMatrix M a.val.2.val).toCoxeterSystem.length w ≤
  (restrictedMatrix M a.val.2.val).toCoxeterSystem.length q)
variable (inj' : Function.Injective (positiveToArtin (restrictedMatrix M a.val.2.val)))
variable (hc : positiveCellTop (restrictedMatrix M a.val.2.val)
  (positiveFullCell (restrictedMatrix M a.val.2.val)) ≠ 1)

include hs in
lemma restrictedFullMatchingLetter :
    (matchingLetter (restrictedMatrix M a.val.2.val) q hq
      ⟨positiveFullCell (restrictedMatrix M a.val.2.val),hc⟩).val = matchingLetter M z hz a := by
  let t := matchingLetter (restrictedMatrix M a.val.2.val) q hq
      ⟨positiveFullCell (restrictedMatrix M a.val.2.val),hc⟩
  apply le_antisymm
  · exact matchingLetter_le_type (restrictedMatrix M a.val.2.val) q hq
      ⟨positiveFullCell (restrictedMatrix M a.val.2.val),hc⟩ ⟨matchingLetter M z hz a,hs⟩ (Set.mem_univ _)
  · exact matchingLetter_le_type M z hz a t.val t.property

include hs in
lemma restrictedFullMatchingFacet :
    restrictedCellEmbedding M a.val.2.val a.val.2.property (positiveToArtin M a.val.1)
      (positiveCellToLifted (restrictedMatrix M a.val.2.val)
        (positiveMatch (restrictedMatrix M a.val.2.val) q hq inj'
          ⟨positiveFullCell (restrictedMatrix M a.val.2.val),hc⟩).val) =
      positiveCellToLifted M (positiveMatch M z hz inj a).val := by
  let N := restrictedMatrix M a.val.2.val
  let c : NoncriticalPositiveCell N := ⟨positiveFullCell N,hc⟩
  let f := restrictedCellEmbedding M a.val.2.val a.val.2.property (positiveToArtin M a.val.1)
  have hfull : f (positiveCellToLifted N c.val) = positiveCellToLifted M a.val := by
    rw [show c.val = positiveFullCell N from rfl,positiveFullCell_lifted]
    exact restrictedCellEmbedding_full M a.val.2.val a.val.2.property _
  apply lifted_same_top_type_unique M
  · apply Subtype.ext
    change Subtype.val '' (positiveMatch N q hq inj' c).val.2.val =
      (positiveMatch M z hz inj a).val.2.val
    rw [positiveMatch_type,matchingOtherType,ite_eq_left (show matchingLetter N q hq c ∈ c.val.2.val from Set.mem_univ _),
      positiveMatch_type,matchingOtherType,ite_eq_left hs]
    have hl := restrictedFullMatchingLetter M z hz a hs q hq hc
    ext t
    constructor
    · rintro ⟨u,hu,rfl⟩
      refine ⟨u.property,?_⟩
      intro he
      apply hu.2
      apply Subtype.ext
      exact he.trans hl.symm
    · rintro ⟨ht,hne⟩
      refine ⟨⟨t,ht⟩,⟨Set.mem_univ _,?_⟩,rfl⟩
      intro he
      apply hne
      exact (congrArg Subtype.val he).trans hl
  · have he := congrArg (positiveToArtin N) (positiveMatch_top N q hq inj' c)
    rw [positiveCellTop_toArtin,positiveCellTop_toArtin] at he
    have he' := congrArg (fun x => positiveToArtin M a.val.1 * restrictedArtinHom M a.val.2.val x) he
    rw [←restrictedCellEmbedding_top M a.val.2.val a.val.2.property,
        ←restrictedCellEmbedding_top M a.val.2.val a.val.2.property] at he'
    change liftedTopVertex M (f _) = liftedTopVertex M _
    rw [he',hfull,←positiveCellTop_toArtin,←positiveCellTop_toArtin,positiveMatch_top]

include hs in

noncomputable def positiveUpperBoundaryRestrictionIso :
    {b : PositiveCellPoset (restrictedMatrix M a.val.2.val) inj' //
      positiveCellToLifted (restrictedMatrix M a.val.2.val) b <
        positiveCellToLifted (restrictedMatrix M a.val.2.val) (positiveFullCell (restrictedMatrix M a.val.2.val)) ∧
      b ≠ (positiveMatch (restrictedMatrix M a.val.2.val) q hq inj'
        ⟨positiveFullCell (restrictedMatrix M a.val.2.val),hc⟩).val} ≃o
    {b : PositiveCellPoset M inj // positiveCellToLifted M b < positiveCellToLifted M a.val ∧
      b ≠ (positiveMatch M z hz inj a).val} := by
  let N := restrictedMatrix M a.val.2.val
  let c : NoncriticalPositiveCell N := ⟨positiveFullCell N,hc⟩
  let f := restrictedCellEmbedding M a.val.2.val a.val.2.property (positiveToArtin M a.val.1)
  have hf : f (positiveCellToLifted N c.val) = positiveCellToLifted M a.val := by
    rw [show c.val = positiveFullCell N from rfl,positiveFullCell_lifted]
    exact restrictedCellEmbedding_full M a.val.2.val a.val.2.property _
  have hm : f (positiveCellToLifted N (positiveMatch N q hq inj' c).val) =
      positiveCellToLifted M (positiveMatch M z hz inj a).val :=
    restrictedFullMatchingFacet M z hz inj a hs q hq inj' hc
  have hsurj : ∀ b ≤ f (positiveCellToLifted N c.val), ∃ t, f t = b := by
    rw [show c.val = positiveFullCell N from rfl,positiveFullCell_lifted]
    exact restrictedCellEmbedding_full_preimage M a.val.2.val a.val.2.property _
  let e := puncturedBoundaryIso f (positiveCellToLifted N c.val)
    (positiveCellToLifted N (positiveMatch N q hq inj' c).val) hsurj
  rw [hf,hm] at e
  exact ((positivePuncturedBoundaryIso N inj' c.val (positiveMatch N q hq inj' c).val).trans e).trans
    (positivePuncturedBoundaryIso M inj a.val (positiveMatch M z hz inj a).val).symm

end HarmonicArtin

end OAI
