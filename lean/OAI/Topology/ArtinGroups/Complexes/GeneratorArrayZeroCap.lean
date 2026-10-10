import Mathlib
import OAI.Topology.ArtinGroups.Complexes.GeneratorArray2
import OAI.Topology.ArtinGroups.Quivers.ClosedNeighborhood
import OAI.Topology.ArtinGroups.Realizations.QuotientFinrankKer

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

omit [Fintype V] [DecidableEq A] in
lemma classGeneratorArray_zero_of_cap (x:FiniteHomotopyClass Q (K:=K))
    (U:Set V) (q:ℤ) (hx:ClassCapOn Q x U q) (p:GeneratorPlacement V)
    (hp:p.color∈U) (hd:q<p.level) : classGeneratorArray Q x p=0 := by
  let E:=minimalClassModel Q x
  have hm:E.complex.IsMinimal Q:=minimalClassModel_minimal Q x
  have hzero:IsEmpty {i:E.Index // E.complex.placement i=p}:=⟨by
    rintro ⟨i,hi⟩
    have hc:(E.complex.placement i).color∈U:=by rw [hi]; exact hp
    have h:=hx i hc
    change (E.complex.placement i).level≤q at h
    rw [hi] at h
    omega⟩
  rw [← minimalClassModel_class Q x,classGeneratorArray_of_minimal Q _ hm,generatorArray_apply]
  exact Nat.card_eq_zero.mpr (Or.inl hzero)

variable {I J:Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

omit [DecidableEq I] [DecidableEq J] in
lemma extremal_socle_forces_top_zero (E:BasedComplex Q (K:=K) I)
    (F:BasedComplex Q (K:=K) J) (hE:E.IsMinimal Q) (hF:F.IsMinimal Q)
    (l q:ℤ) (hb:∀i j,(E.placement i).color=(F.placement j).color→
      (F.placement j).level-(E.placement i).level≤q-l)
    (hz:∀n v,n+v=q-l+2→homDimension Q E F n v=0)
    (α:V) (c d:ℤ)
    (hs:coefficientSocle Q (E.pureLayer Q hE l) α d≠⊥) :
    coefficientTopDual Q (F.pureLayer Q hF q) α c=⊥ := by
  by_contra ht
  have hp:=pure_top_socle_homDimension_pos Q (F.pureLayer Q hF q) (E.pureLayer Q hE l)
    (fun i=>i.property) (fun i=>i.property) α c d ht hs
  have hd:=homDimension_dual Q (E.pureLayer Q hE l) (F.pureLayer Q hF q)
    (c-d) (q-l-(c-d)+2)
  have hp':0<homDimension Q (E.pureLayer Q hE l) (F.pureLayer Q hF q)
      (c-d) (q-l-(c-d)+2) := by
    rw [hd]
    convert hp using 1
    congr 1 <;> omega
  have hl:=tokenLayer_homDimension_le Q E F hE hF l q
    (c-d) (q-l-(c-d)+2) (by omega) hb
  rw [hz _ _ (by omega)] at hl
  omega

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
