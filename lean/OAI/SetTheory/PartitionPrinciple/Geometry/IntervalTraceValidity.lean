import OAI.SetTheory.PartitionPrinciple.Definability.IntervalSequenceFormulas

namespace OAI

section

namespace PartitionPilot.Forcing

universe u

theorem intervalSequence_of_next
    {N A D rA rD e lo hi t : ZFSet.{u}}
    (source : StrictLinearOrderCode A rA) (target : StrictLinearOrderCode D rD)
    (enumeration : ZFSet.IsFunc ZFSet.omega A e)
    (natural : N ⊆ ZFSet.omega) (function : FunctionGraphOn N t)
    (next : ∀ i ∈ N, ∀ y, ZFSet.pair i y ∈ t →
      intervalNextCandidate i A D rA rD e lo hi (graphRestriction i t) y) :
    IntervalSequenceCode N A D rA rD e lo hi t := by
  have functionD : ZFSet.IsFunc N D t := by
    refine ⟨?_, function.to_isFunc.2⟩
    intro w hw
    obtain ⟨i, hiN, y, rfl⟩ := function.shape w hw
    exact ZFSet.pair_mem_prod.2 ⟨hiN, (next i hiN y hw).1⟩
  have pairwise : ∀ i j a b q z,
      ZFSet.pair i a ∈ e → ZFSet.pair j b ∈ e →
      ZFSet.pair i q ∈ t → ZFSet.pair j z ∈ t →
      (a = b ↔ q = z) ∧ (ZFSet.pair a b ∈ rA ↔ ZFSet.pair q z ∈ rD) ∧
        (ZFSet.pair b a ∈ rA ↔ ZFSet.pair z q ∈ rD) := by
    intro i j a b q z ia jb iq jz
    have iN := function.pair_source iq
    have jN := function.pair_source jz
    have aA := (ZFSet.pair_mem_prod.1 (enumeration.1 ia)).2
    have bA := (ZFSet.pair_mem_prod.1 (enumeration.1 jb)).2
    have qD := (ZFSet.pair_mem_prod.1 (functionD.1 iq)).2
    have zD := (ZFSet.pair_mem_prod.1 (functionD.1 jz)).2
    obtain ⟨m, rfl⟩ := (mem_omega_iff_natSetCode i).1 (natural iN)
    obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode j).1 (natural jN)
    rcases lt_trichotomy m n with earlier | same | later
    · exact (next (natSetCode n) jN z jz).2.2.2
        (natSetCode m) ((natSetCode_mem_iff m n).2 earlier)
        a aA b bA q qD ia jb (pair_mem_graphRestriction.2 ⟨iq,
          (natSetCode_mem_iff m n).2 earlier⟩)
    · subst n
      have equalSource : a = b := (show FunctionGraphOn ZFSet.omega e from ⟨A, enumeration⟩).unique ia jb
      have equalTarget : q = z := function.unique iq jz
      subst b
      subst z
      exact ⟨iff_of_true rfl rfl,
        iff_of_false (source.irrefl a aA) (target.irrefl q qD),
        iff_of_false (source.irrefl a aA) (target.irrefl q qD)⟩
    · have reversed := (next (natSetCode m) iN q iq).2.2.2
        (natSetCode n) ((natSetCode_mem_iff n m).2 later)
        b bA a aA z zD jb ia (pair_mem_graphRestriction.2 ⟨jz,
          (natSetCode_mem_iff n m).2 later⟩)
      exact ⟨by simpa only [eq_comm] using reversed.1, reversed.2.2, reversed.2.1⟩
  refine ⟨functionD, ?_, ?_, ?_⟩
  · intro i y iy
    have candidate := next i (function.pair_source iy) y iy
    exact ⟨candidate.2.1, candidate.2.2.1⟩
  · intro i j a b q z ia jb iq jz
    exact (pairwise i j a b q z ia jb iq jz).1
  · intro i j a b q z ia jb iq jz
    exact (pairwise i j a b q z ia jb iq jz).2.1

end PartitionPilot.Forcing

end

end OAI
