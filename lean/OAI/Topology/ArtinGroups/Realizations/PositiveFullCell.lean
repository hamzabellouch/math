import Mathlib
import OAI.Topology.ArtinGroups.Realizations.FullSphericalCell
import OAI.Topology.ArtinGroups.Harmonic.PositiveEarlierLinkUpper

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type*} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)
variable (z : M.Group) (hz : ∀ w, M.toCoxeterSystem.length w ≤ M.toCoxeterSystem.length z)
variable (inj : Function.Injective (positiveToArtin M))

lemma positiveMatch_coatom (a : NoncriticalPositiveCell M)
    (hs : matchingLetter M z hz a ∈ a.val.2.val) (b : PositiveCellPoset M inj)
    (hdb : positiveCellToLifted M (positiveMatch M z hz inj a).val ≤ positiveCellToLifted M b)
    (hba : positiveCellToLifted M b < positiveCellToLifted M a.val) :
    b = (positiveMatch M z hz inj a).val := by
  by_contra hne
  have hlt : positiveCellToLifted M (positiveMatch M z hz inj a).val < positiveCellToLifted M b :=
    lt_of_le_of_ne hdb (fun he => hne (positiveCellToLifted_injective M inj he).symm)
  have h1 := lifted_rank_strict M hlt
  have h2 := lifted_rank_strict M hba
  change (positiveMatch M z hz inj a).val.2.val.ncard < b.2.val.ncard at h1
  change b.2.val.ncard < a.val.2.val.ncard at h2
  rw [positiveMatch_type,matchingOtherType,ite_eq_left hs] at h1
  have hc := Set.ncard_sdiff_singleton_add_one hs (Set.toFinite a.val.2.val)
  omega

variable [Finite M.Group]

noncomputable def positiveFullCell : PositiveLiftedCell M := (1,(fullSphericalCell M).2)

omit [Fintype S] [LinearOrder S] in
lemma positiveFullCell_lifted : positiveCellToLifted M (positiveFullCell M) = fullSphericalCell M := by
  exact Prod.ext (map_one (positiveToArtin M)) rfl

omit [LinearOrder S] in
lemma positiveFullCell_top : positiveCellTop M (positiveFullCell M) =
    positiveSimpleLift M (sphericalLongest M (fullSphericalCell M).2) := by
  exact one_mul _

omit [LinearOrder S] in
lemma positiveFullCell_noncritical (s : S) : positiveCellTop M (positiveFullCell M) ≠ 1 := by
  intro h
  have he := (positiveCellTop_eq_one_iff M _).mp h
  have ht := congrArg (fun a : PositiveLiftedCell M => a.2.val) he
  change (Set.univ : Set S) = ∅ at ht
  exact Set.notMem_empty s (ht ▸ Set.mem_univ s)

lemma positiveMatch_face_full (a : NoncriticalPositiveCell M)
    (h : positiveCellToLifted M a.val ≤ fullSphericalCell M) :
    positiveCellToLifted M (positiveMatch M z hz inj a).val ≤ fullSphericalCell M := by
  apply (lifted_le_iff_face M _ _).mpr
  apply positiveCell_face_full_of_top_prefix
  rw [positiveMatch_top,←positiveFullCell_top]
  apply positiveCellTop_prefix_of_face M inj
  rw [positiveFullCell_lifted]
  exact (lifted_le_iff_face M _ _).mp h

lemma positiveFullBoundary_down (hc : positiveCellTop M (positiveFullCell M) ≠ 1)
    {a b : PositiveCellPoset M inj} (hab : a ≤ b)
    (hb : positiveCellToLifted M b < fullSphericalCell M ∧
      b ≠ (positiveMatch M z hz inj ⟨positiveFullCell M,hc⟩).val) :
    positiveCellToLifted M a < fullSphericalCell M ∧
      a ≠ (positiveMatch M z hz inj ⟨positiveFullCell M,hc⟩).val := by
  change positiveCellToLifted M a ≤ positiveCellToLifted M b at hab
  refine ⟨hab.trans_lt hb.1,?_⟩
  intro he
  apply hb.2
  apply positiveMatch_coatom M z hz inj ⟨positiveFullCell M,hc⟩ (Set.mem_univ _) b
  · simpa only [he] using hab
  · simpa only [positiveFullCell_lifted] using hb.1

lemma positiveFullBoundary_match (hc : positiveCellTop M (positiveFullCell M) ≠ 1)
    (a : NoncriticalPositiveCell M)
    (ha : positiveCellToLifted M a.val < fullSphericalCell M ∧
      a.val ≠ (positiveMatch M z hz inj ⟨positiveFullCell M,hc⟩).val) :
    positiveCellToLifted M (positiveMatch M z hz inj a).val < fullSphericalCell M ∧
      (positiveMatch M z hz inj a).val ≠ (positiveMatch M z hz inj ⟨positiveFullCell M,hc⟩).val := by
  have hle := positiveMatch_face_full M z hz inj a ha.1.le
  refine ⟨lt_of_le_of_ne hle ?_,?_⟩
  · intro he
    have hm : (positiveMatch M z hz inj a).val = positiveFullCell M :=
      positiveCellToLifted_injective M inj (he.trans (positiveFullCell_lifted M).symm)
    exact ha.2 (positiveMatch_symm_value M z hz inj a ⟨positiveFullCell M,hc⟩ hm).symm
  · intro he
    have hh := congrArg (positiveMatch M z hz inj) (Subtype.ext he)
    rw [positiveMatch_involutive,positiveMatch_involutive] at hh
    have hh' := congrArg (fun a : NoncriticalPositiveCell M => positiveCellToLifted M a.val) hh
    rw [positiveFullCell_lifted] at hh'
    exact ha.1.ne hh'

lemma positiveFullBoundary_root (hc : positiveCellTop M (positiveFullCell M) ≠ 1) :
    positiveCellToLifted M (positiveRootCell M) < fullSphericalCell M ∧
      positiveRootCell M ≠ (positiveMatch M z hz inj ⟨positiveFullCell M,hc⟩).val := by
  have hr : positiveCellTop M (positiveRootCell M) = 1 := (positiveCellTop_eq_one_iff M _).mpr rfl
  have hle : positiveCellToLifted M (positiveRootCell M) ≤ fullSphericalCell M := by
    apply (lifted_le_iff_face M _ _).mpr
    apply positiveCell_face_full_of_top_prefix
    rw [hr]
    exact ⟨_,(one_mul _).symm⟩
  refine ⟨lt_of_le_of_ne hle ?_,?_⟩
  · intro he
    have hh := positiveCellToLifted_injective M inj (he.trans (positiveFullCell_lifted M).symm)
    exact hc (by rw [←hh,hr])
  · intro he
    have hh := positiveMatch_top M z hz inj ⟨positiveFullCell M,hc⟩
    rw [←he,hr] at hh
    exact hc hh.symm

end HarmonicArtin

end OAI
