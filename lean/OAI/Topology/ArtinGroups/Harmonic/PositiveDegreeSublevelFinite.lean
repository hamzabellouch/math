import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.PositivePrefix

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] (M:CoxeterMatrix S)

theorem positive_degree_sublevel_finite (n:ℕ) :
    {a:PositiveArtin M | positiveDegree M a≤n}.Finite := by
  have h:({w:List S | w.length≤n}).Finite:=List.finite_length_le S n
  apply (h.image (wordPositive M)).subset
  intro a ha
  obtain ⟨w,rfl⟩:=positive_word_surjective M a
  exact ⟨w,by simpa only [Set.mem_ofPred_eq,positiveDegree_word] using ha,rfl⟩

theorem positive_lifted_sublevel_finite (g:Artin M) (n:ℕ) :
    {a:LiftedCell M | ∃p:PositiveArtin M,positiveDegree M p≤n ∧
      a.1=g*positiveToArtin M p}.Finite := by
  let P:Set (Artin M):=(fun p:PositiveArtin M=>g*positiveToArtin M p) ''
    {p:PositiveArtin M | positiveDegree M p≤n}
  have hP:P.Finite:=(positive_degree_sublevel_finite M n).image _
  have hT:(Set.univ:Set (SphericalType M)).Finite:=Set.toFinite _
  apply (hP.prod hT).subset
  rintro a ⟨p,hp,he⟩
  exact ⟨⟨p,hp,he.symm⟩,Set.mem_univ _⟩

omit [Fintype S] in
theorem positive_strictPrefix_wellFounded :
    WellFounded (fun a b:PositiveArtin M=>PositivePrefix M a b ∧ a≠b) := by
  apply (measure (positiveDegree M)).wf.mono
  intro a b h
  have hl:=positivePrefix_degree M h.1
  exact lt_of_le_of_ne hl (fun he=>h.2 (positivePrefix_eq_of_degree M h.1 he))

omit [Fintype S] in
theorem positive_lcm_of_common_multiple
    (gcd:∀a b:PositiveArtin M,∃g:PositiveArtin M,
      PositivePrefix M g a ∧ PositivePrefix M g b ∧
      ∀e:PositiveArtin M,PositivePrefix M e a→PositivePrefix M e b→PositivePrefix M e g)
    (a b:PositiveArtin M)
    (hex:∃c:PositiveArtin M,PositivePrefix M a c ∧ PositivePrefix M b c) :
    ∃c:PositiveArtin M,PositivePrefix M a c ∧ PositivePrefix M b c ∧
      ∀d:PositiveArtin M,PositivePrefix M a d→PositivePrefix M b d→PositivePrefix M c d := by
  let P:ℕ→Prop:=fun n=>∃c:PositiveArtin M,PositivePrefix M a c ∧ PositivePrefix M b c ∧ positiveDegree M c=n
  have hP:∃n,P n:=by obtain ⟨c,hac,hbc⟩:=hex;exact ⟨positiveDegree M c,c,hac,hbc,rfl⟩
  obtain ⟨c,hac,hbc,hc⟩:=Nat.find_spec hP
  refine ⟨c,hac,hbc,?_⟩
  intro d had hbd
  obtain ⟨e,hec,hed,he⟩:=gcd c d
  have hae:=he a hac had
  have hbe:=he b hbc hbd
  have hmin:positiveDegree M c≤positiveDegree M e:=by
    rw [hc]
    exact Nat.find_min' hP ⟨e,hae,hbe,rfl⟩
  have heq:e=c:=positivePrefix_eq_of_degree M hec (Nat.le_antisymm (positivePrefix_degree M hec) hmin)
  rwa [heq] at hed

end HarmonicArtin

end OAI
