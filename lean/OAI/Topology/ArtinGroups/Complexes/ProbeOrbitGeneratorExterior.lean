import Mathlib
import OAI.Topology.ArtinGroups.Quivers.ProbeSwapIso
import OAI.Topology.ArtinGroups.Complexes.IsolatedIndexCycle
import OAI.Topology.ArtinGroups.Quivers.ProbeLeaf

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A:Type} {K:Type*} [Field K] [Fintype V] [Fintype A]
  (Q:ReversibleQuiver V A) (hn:∀a,Q.source a≠Q.target a)
attribute [local instance] Classical.decEq Classical.propDecidable
local notation "R" => probeQuiver Q

lemma probeOrbit_generator_exterior (w:List (V×Bool)) (α β:V) (b c:Bool) (n u:ℤ) :
    classGeneratorArray R (probeOrbit Q (K:=K) hn w α b) ⟨.inr (β,c),n,u⟩=
      if β=α ∧ c=b ∧ n=0 ∧ u=0 then 1 else 0 := by
  rw [probeOrbit,probeWordPerm_exterior Q hn w _ _ β c rfl,classGeneratorArray_initial]
  simp only [GeneratorPlacement.mk.injEq,Sum.inr.injEq,Prod.mk.injEq,and_assoc]

theorem probeOrbit_fixed_of_no_diagonal (w:List (V×Bool)) (α:V) (b:Bool)
    (hz:∀n u,classGeneratorArray R (probeOrbit Q (K:=K) hn w α b) ⟨.inl α,n,u⟩=0) :
    probeOrbit Q (K:=K) hn w α b=initialClass R (.inr (α,b)) := by
  let x:=probeOrbit Q (K:=K) hn w α b
  let E:=minimalClassModel R x
  have hm:E.complex.IsMinimal R:=minimalClassModel_minimal R x
  have harray:E.complex.generatorArray R=classGeneratorArray R x := by
    rw [← minimalClassModel_class R x,classGeneratorArray_of_minimal R _ hm]
  have hpos:∀i,0<classGeneratorArray R x (E.complex.placement i) := by
    intro i
    rw [← harray]
    exact generatorArray_placement_pos Q _ i
  have hout:∀n u,classGeneratorArray R x ⟨.inr (α,b),n,u⟩=
      if n=0 ∧ u=0 then 1 else 0 := by
    intro n u
    simp only [x,probeOrbit_generator_exterior,true_and]
  have hone:E.complex.generatorArray R ⟨.inr (α,b),0,0⟩=1 := by
    rw [harray,hout]; simp
  rw [generatorArray_apply] at hone
  change Nat.card {i:E.Index // E.complex.placement i=⟨.inr (α,b),0,0⟩}=1 at hone
  have :Nonempty {i:E.Index // E.complex.placement i=⟨.inr (α,b),0,0⟩} :=
    (Nat.card_pos_iff.mp (show 0<Nat.card {i:E.Index // E.complex.placement i=⟨.inr (α,b),0,0⟩} by omega)).1
  obtain ⟨i,hi⟩:=‹Nonempty {i:E.Index // E.complex.placement i=⟨.inr (α,b),0,0⟩}›
  have hcore:∀j,(E.complex.placement j).color≠.inl α := by
    intro j hj
    have hp:=hpos j
    have hp' := hz (E.complex.placement j).cochain (E.complex.placement j).internal
    have he:E.complex.placement j=⟨.inl α,(E.complex.placement j).cochain,
        (E.complex.placement j).internal⟩ := by rw [← hj]
    rw [he] at hp
    change 0<classGeneratorArray R (probeOrbit Q (K:=K) hn w α b) _ at hp
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
    change classHomDimension R 0 0
      (probeWordPerm Q hn w (initialClass R (.inr (α,b))))
      (probeWordPerm Q hn w (initialClass R (.inr (α,b))))≤1
    rw [probeWordPerm_homDimension]
    exact initial_homDimension_le_one R (probeQuiver_no_loops Q hn) (.inr (α,b)) 0 0
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
  calc x=classOfComplex R E.complex := (minimalClassModel_class R x).symm
       _=classOfComplex R (E.complex.reindex R e) := classOfComplex_reindex R E.complex e
       _=initialClass R (.inr (α,b)) := by rw [he]; rfl

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
