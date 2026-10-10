import Mathlib
import OAI.Topology.ArtinGroups.Realizations.PositiveRootCell

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)
variable (z:M.Group) (hz:∀w,M.toCoxeterSystem.length w≤M.toCoxeterSystem.length z)
variable (inj:Function.Injective (positiveToArtin M))

def ActualPositiveGradientStep (a b:PositiveLiftedCell M) : Prop :=
  (∃ha:positiveCellTop M a≠1,
    matchingLetter M z hz ⟨a,ha⟩ ∉ a.2.val ∧
    (positiveMatch M z hz inj ⟨a,ha⟩).val=b) ∨
  (positiveCellToLifted M b≤positiveCellToLifted M a ∧
    a.2.val.toFinset.card=b.2.val.toFinset.card+1 ∧
    ¬∃hb:positiveCellTop M b≠1,(positiveMatch M z hz inj ⟨b,hb⟩).val=a)

lemma actualPositiveGradientStep_sub {a b:PositiveLiftedCell M}
    (h:ActualPositiveGradientStep M z hz inj a b) : PositiveGradientStep M z hz a b := by
  rcases h with ⟨ha,hs,he⟩|⟨hle,hcard,hn⟩
  · rw [←he]
    exact positiveMatch_gradient M z hz inj ⟨a,ha⟩ hs
  · by_cases he:positiveCellTop M b=positiveCellTop M a
    · have ha:positiveCellTop M a≠1:=by
        intro ha
        have hb:=he.trans ha
        rw [(positiveCellTop_eq_one_iff M a).mp ha,
          (positiveCellTop_eq_one_iff M b).mp hb] at hcard
        omega
      have hb:positiveCellTop M b≠1:=fun hb=>ha (he.symm.trans hb)
      have hsub:b.2.val.toFinset⊆a.2.val.toFinset:=by
        intro s hs
        exact Set.mem_toFinset.mpr (((lifted_le_iff_face M _ _).mp hle).1 (Set.mem_toFinset.mp hs))
      obtain ⟨t,ht,hte⟩:=Finset.exists_eq_insert_iff.mpr ⟨hsub,hcard.symm⟩
      have hne:t≠firstPositiveDescent M z hz (positiveCellTop M a) ha:=by
        intro hts
        apply hn
        refine ⟨hb,?_⟩
        apply positiveCell_same_top_type_unique M inj
        · apply Subtype.ext
          rw [positiveMatch_type]
          have hbs:matchingLetter M z hz ⟨b,hb⟩=t:=by simp only [matchingLetter,he,hts]
          have hnot:matchingLetter M z hz ⟨b,hb⟩∉b.2.val:=by
            rw [hbs]
            exact fun h=>ht (Set.mem_toFinset.mpr h)
          rw [matchingOtherType,ite_eq_right hnot,hbs]
          ext s
          simpa only [Set.mem_toFinset,Finset.mem_insert,Set.mem_insert_iff] using Finset.ext_iff.mp hte s
        · exact (positiveMatch_top M z hz inj ⟨b,hb⟩).trans he
      exact Or.inr ⟨ha,he,Or.inr ⟨t,hne,ht,hte.symm⟩⟩
    · exact Or.inl ⟨hle,he⟩

theorem actualPositiveGradient_wellFounded :
    WellFounded (fun b a:PositiveLiftedCell M=>ActualPositiveGradientStep M z hz inj a b) :=
  (positiveGradient_wellFounded M z hz inj).mono (fun _ _ h=>actualPositiveGradientStep_sub M z hz inj h)

end HarmonicArtin

end OAI
