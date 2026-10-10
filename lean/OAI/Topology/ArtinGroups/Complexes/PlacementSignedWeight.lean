import Mathlib
import OAI.Topology.ArtinGroups.Cancellation.Retained
import OAI.Topology.ArtinGroups.Complexes.FiniteHomotopySetoid
import OAI.Topology.ArtinGroups.Complexes.GeneratorArray
import OAI.Topology.ArtinGroups.Complexes.HomSpace

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

noncomputable def placementSignedWeight (a : GeneratorPlacement V) (v : V) : ℝ :=
  if a.color=v then cochainSign a.level else 0

noncomputable def signedGeneratorVector {I : Type u} [Fintype I]
    (E : BasedComplex Q (K:=K) I) (v : V) : ℝ :=
  ∑ i, placementSignedWeight (E.placement i) v

omit [Fintype V] [DecidableEq A] in
lemma signedGeneratorVector_array {I : Type u} [Fintype I]
    (E : BasedComplex Q (K:=K) I) (v : V) :
    signedGeneratorVector Q E v=
      Finsupp.liftAddHom (fun a => multiplesHom ℝ (placementSignedWeight a v)) (E.generatorArray Q) := by
  simp only [signedGeneratorVector,generatorArray,map_sum,Finsupp.liftAddHom_apply_single]
  simp

omit [Fintype V] [DecidableEq A] in
lemma signedGeneratorVector_minimal_eq {I J : Type u} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (E : BasedComplex Q (K:=K) I) (F : BasedComplex Q (K:=K) J)
    (hE : E.IsMinimal Q) (hF : F.IsMinimal Q) (e : HomotopyEquivalence Q E F) :
    signedGeneratorVector Q E=signedGeneratorVector Q F := by
  funext v
  rw [signedGeneratorVector_array,signedGeneratorVector_array,
    generatorArray_eq_of_minimal_homotopyEquivalence Q E F hE hF e]

omit [Fintype V] [DecidableEq A] in
lemma ScalarPivot.signedWeight_cancel {I : Type u} [Fintype I]
    {E : BasedComplex Q (K:=K) I} (p : ScalarPivot Q E) (v : V) :
    placementSignedWeight (E.placement p.source) v+
      placementSignedWeight (E.placement p.target) v=0 := by
  have hl : (E.placement p.target).level=(E.placement p.source).level+1 := by
    simp only [GeneratorPlacement.level,p.cochain,p.internal]
    omega
  simp only [placementSignedWeight,p.color,hl,cochainSign_add_one]
  split_ifs <;> ring

omit [Fintype V] [DecidableEq A] in
lemma ScalarPivot.signedGeneratorVector_reduced {I : Type u} [Fintype I] [DecidableEq I]
    {E : BasedComplex Q (K:=K) I} (p : ScalarPivot Q E) :
    signedGeneratorVector Q (p.reduced Q)=signedGeneratorVector Q E := by
  funext v
  let f : I → ℝ := fun i => placementSignedWeight (E.placement i) v
  have hs : ∑ i : p.Retained Q, f i =
      ∑ i ∈ ((Finset.univ : Finset I).erase p.source).erase p.target, f i := by
    symm
    apply Finset.sum_subtype
    intro i
    simp [and_comm]
  change (∑ i : p.Retained Q, f i)=∑ i, f i
  rw [hs]
  have h1 := Finset.sum_erase_add (Finset.univ : Finset I) f (Finset.mem_univ p.source)
  have h2 := Finset.sum_erase_add ((Finset.univ : Finset I).erase p.source) f
    (by simp [p.distinct.symm] : p.target∈(Finset.univ : Finset I).erase p.source)
  have hc := p.signedWeight_cancel Q v
  change f p.source + f p.target=0 at hc
  linarith

namespace FiniteModel

omit [Fintype V] [DecidableEq A] in
theorem exists_minimal_signed (E : FiniteModel.{u} Q (K:=K)) :
    ∃ F : FiniteModel.{u} Q (K:=K), F.complex.IsMinimal Q ∧
      Nonempty (HomotopyEquivalence Q E.complex F.complex) ∧
      signedGeneratorVector Q E.complex=signedGeneratorVector Q F.complex := by
  have h : ∀ n (B : FiniteModel.{u} Q (K:=K)), Fintype.card B.Index=n →
      ∃ F : FiniteModel.{u} Q (K:=K), F.complex.IsMinimal Q ∧
        Nonempty (HomotopyEquivalence Q B.complex F.complex) ∧
        signedGeneratorVector Q B.complex=signedGeneratorVector Q F.complex := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro B hn
      by_cases hm : B.complex.IsMinimal Q
      · exact ⟨B,hm,⟨HomotopyEquivalence.refl Q B.complex⟩,rfl⟩
      obtain ⟨p⟩ := scalarPivot_of_not_minimal Q B.complex hm
      let C := ofComplex Q (p.reduced Q)
      have hc : Fintype.card C.Index<n := by
        dsimp only [C,ofComplex]
        rw [← hn]
        exact p.retained_card_lt Q
      obtain ⟨F,hF,⟨e⟩,hs⟩ := ih (Fintype.card C.Index) hc C rfl
      exact ⟨F,hF,⟨(p.reductionEquivalence Q).trans Q e⟩,
        (p.signedGeneratorVector_reduced Q).symm.trans hs⟩
  exact h (Fintype.card E.Index) E rfl

omit [Fintype V] [DecidableEq A] in
lemma signedGeneratorVector_homotopy (E F : FiniteModel.{u} Q (K:=K))
    (e : HomotopyEquivalence Q E.complex F.complex) :
    signedGeneratorVector Q E.complex=signedGeneratorVector Q F.complex := by
  obtain ⟨E',hE',⟨eE⟩,hsE⟩ := E.exists_minimal_signed Q
  obtain ⟨F',hF',⟨eF⟩,hsF⟩ := F.exists_minimal_signed Q
  rw [hsE,hsF]
  exact signedGeneratorVector_minimal_eq Q _ _ hE' hF'
    ((eE.symm Q).trans Q (e.trans Q eF))

end FiniteModel

noncomputable def classSignedVector : FiniteHomotopyClass Q (K:=K) → (V → ℝ) :=
  Quotient.lift (fun E => signedGeneratorVector Q E.complex)
    (fun E F h => by obtain ⟨e⟩:=h; exact FiniteModel.signedGeneratorVector_homotopy Q E F e)

omit [Fintype V] [DecidableEq A] in
lemma classSignedVector_mk (E : FiniteModel.{u} Q (K:=K)) :
    classSignedVector Q (Quotient.mk (finiteHomotopySetoid Q) E)=signedGeneratorVector Q E.complex := rfl

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
