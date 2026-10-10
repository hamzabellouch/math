import Mathlib
import OAI.Topology.ArtinGroups.Complexes.MinimalModel
import OAI.Topology.ArtinGroups.Complexes.BasedComplexComplex
import OAI.Topology.ArtinGroups.Complexes.IsolatedIndexCycle
import OAI.Topology.ArtinGroups.Quivers.ProbeLeaf

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A:Type} {K:Type*} [Field K] [Fintype V] [Fintype A]
  (Q:ReversibleQuiver V A) [DecidableEq (ProbeVertex V)]
attribute [local instance] Classical.decEq Classical.propDecidable
local notation "R" => probeQuiver Q

theorem probeClass_fixed_of_no_diagonal (x:FiniteHomotopyClass R (K:=K))
    (α:V) (b:Bool)
    (hz:∀n u,classGeneratorArray R x ⟨.inl α,n,u⟩=0)
    (hout:∀n u,classGeneratorArray R x ⟨.inr (α,b),n,u⟩=if n=0 ∧ u=0 then 1 else 0)
    (hdim:classHomDimension R 0 0 x x≤1) : x=initialClass R (.inr (α,b)) := by
  cases Subsingleton.elim (inferInstance : DecidableEq (ProbeVertex V))
    (@instDecidableEqSum V (V×Bool) (Classical.decEq V)
      (@instDecidableEqProd V Bool (Classical.decEq V) inferInstance))
  let : DecidableEq (ProbeVertex V) :=
    @instDecidableEqSum V (V×Bool) (Classical.decEq V)
      (@instDecidableEqProd V Bool (Classical.decEq V) inferInstance)
  let E:=minimalClassModel R x
  have hm:E.complex.IsMinimal R:=minimalClassModel_minimal R x
  have harray:E.complex.generatorArray R=classGeneratorArray R x := by
    calc
      _ = classGeneratorArray R (Quotient.mk (finiteHomotopySetoid R) E) :=
        (classGeneratorArray_of_minimal R E hm).symm
      _ = _ := congrArg (classGeneratorArray R) (minimalClassModel_class R x)
  have hpos:∀i,0<classGeneratorArray R x (E.complex.placement i) := by
    intro i
    rw [← harray]
    exact generatorArray_placement_pos Q _ i
  have hone:E.complex.generatorArray R ⟨.inr (α,b),0,0⟩=1 := by
    rw [harray,hout]; simp
  rw [generatorArray_apply] at hone
  change Nat.card {i:E.Index // E.complex.placement i=⟨.inr (α,b),0,0⟩}=1 at hone
  have : Nonempty {i:E.Index // E.complex.placement i=⟨.inr (α,b),0,0⟩} :=
    (Nat.card_pos_iff.mp (show 0<Nat.card {i:E.Index // E.complex.placement i=⟨.inr (α,b),0,0⟩} by omega)).1
  obtain ⟨i,hi⟩:=‹Nonempty {i:E.Index // E.complex.placement i=⟨.inr (α,b),0,0⟩}›
  have hcore:∀j,(E.complex.placement j).color≠.inl α := by
    intro j hj
    have hp:=hpos j
    have hp' := hz (E.complex.placement j).cochain (E.complex.placement j).internal
    have he:E.complex.placement j=⟨.inl α,(E.complex.placement j).cochain,
        (E.complex.placement j).internal⟩ := by rw [← hj]
    rw [he] at hp
    change 0<classGeneratorArray R x _ at hp
    omega
  have hf:∀j,(E.complex.placement j).color=.inr (α,b)→(E.complex.placement j).cochain=0 := by
    intro j hj
    have hp:=hpos j
    have he:E.complex.placement j=⟨.inr (α,b),(E.complex.placement j).cochain,
        (E.complex.placement j).internal⟩ := by rw [← hj]
    rw [he,hout] at hp
    split_ifs at hp with h
    · exact h.1
    · omega
  have hr:∀j,E.complex.differential i j=0:=
    probe_differential_row_zero Q E.complex α b hcore hf i (congrArg GeneratorPlacement.color hi)
  have hc:∀j,E.complex.differential j i=0:=
    probe_differential_col_zero Q E.complex α b hcore hf i (congrArg GeneratorPlacement.color hi)
  have hd:homDimension R E.complex E.complex 0 0≤1 := by
    change homDimension R (minimalClassModel R x).complex (minimalClassModel R x).complex 0 0≤1
    rw [minimalClassModel_homDimension]
    exact hdim
  have hall:∀j:E.Index,j=i:=eq_isolated_index R E.complex hm hd i hr hc
  let e:PUnit.{1}≃E.Index :=
    { toFun:=fun _=>i,invFun:=fun _=>PUnit.unit,
      left_inv:=fun _=>rfl,right_inv:=fun j=>(hall j).symm }
  have he:E.complex.reindex R e=initialProjective R (.inr (α,b)) := by
    apply ext_placement_differential R
    · funext j
      exact hi
    · apply Matrix.ext
      intro j k
      exact hr i
  have h₁ : x=classOfComplex R E.complex := (minimalClassModel_class R x).symm
  have h₂ : classOfComplex R E.complex=classOfComplex R (E.complex.reindex R e) :=
    classOfComplex_reindex R E.complex e
  have h₃ : classOfComplex R (E.complex.reindex R e)=initialClass R (.inr (α,b)) := by
    rw [he]; rfl
  exact h₁.trans (h₂.trans h₃)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
