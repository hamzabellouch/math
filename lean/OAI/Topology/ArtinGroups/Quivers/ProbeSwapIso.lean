import Mathlib
import OAI.Topology.ArtinGroups.Complexes.MinimalModel
import OAI.Topology.ArtinGroups.Functors.ComplexInitial
import OAI.Topology.ArtinGroups.Functors.ComplexPureLayer
import OAI.Topology.ArtinGroups.Harmonic.FinsuppMapDomainFiber
import OAI.Topology.ArtinGroups.Complexes.PacketPermExterior
import OAI.Topology.ArtinGroups.Quivers.ProbeVertex

namespace OAI

namespace HarmonicArtin.ReversibleQuiver
variable {V A:Type} (Q:ReversibleQuiver V A)
attribute [local instance] Classical.decEq Classical.propDecidable

def probeSwapIso : Iso (probeQuiver Q) (probeQuiver Q) where
  vertex :=
    { toFun := Sum.map id (fun p => (p.1,!p.2))
      invFun := Sum.map id (fun p => (p.1,!p.2))
      left_inv := by rintro (v|⟨v,b⟩) <;> simp
      right_inv := by rintro (v|⟨v,b⟩) <;> simp }
  arrow :=
    { toFun := Sum.map id (fun p => (p.1,!p.2.1,p.2.2))
      invFun := Sum.map id (fun p => (p.1,!p.2.1,p.2.2))
      left_inv := by rintro (a|⟨v,b,d⟩) <;> simp
      right_inv := by rintro (a|⟨v,b,d⟩) <;> simp }
  source := by
    rintro (a|⟨v,b,d⟩)
    · rfl
    · cases d <;> rfl
  target := by
    rintro (a|⟨v,b,d⟩)
    · rfl
    · cases d <;> rfl
  reverse := by
    rintro (a|⟨v,b,d⟩) <;> rfl

namespace Zigzag.BasedComplex
variable {K:Type*} [Field K] [Fintype V] [Fintype A]
local notation "R" => probeQuiver Q
variable (hn:∀a,Q.source a≠Q.target a)
local notation "hnR" => probeQuiver_no_loops Q hn

noncomputable def probeSignedPerm (a:V×Bool) : Equiv.Perm (FiniteHomotopyClass R (K:=K)) :=
  if a.2 then classTwistPerm R hnR (.inl a.1) else (classTwistPerm R hnR (.inl a.1)).symm

noncomputable def probeWordPerm : List (V×Bool) → Equiv.Perm (FiniteHomotopyClass R (K:=K))
  | [] => 1
  | a::w => probeSignedPerm Q hn a * probeWordPerm w

noncomputable def probeOrbit (w:List (V×Bool)) (α:V) (b:Bool) : FiniteHomotopyClass R (K:=K) :=
  probeWordPerm Q hn w (initialClass R (.inr (α,b)))

lemma probeSignedPerm_homDimension (a:V×Bool) (x y:FiniteHomotopyClass R (K:=K)) (n v:ℤ) :
    classHomDimension R n v (probeSignedPerm Q hn a x) (probeSignedPerm Q hn a y)=
      classHomDimension R n v x y := by
  unfold probeSignedPerm
  split_ifs
  · exact classPositiveTwist_homDimension R hnR _ n v x y
  · exact classNegativeTwist_homDimension R hnR _ n v x y

lemma probeWordPerm_homDimension (w:List (V×Bool)) (x y:FiniteHomotopyClass R (K:=K)) (n v:ℤ) :
    classHomDimension R n v (probeWordPerm Q hn w x) (probeWordPerm Q hn w y)=
      classHomDimension R n v x y := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    change classHomDimension R n v (probeSignedPerm Q hn a _) (probeSignedPerm Q hn a _)=_
    rw [probeSignedPerm_homDimension,ih]

lemma probeSignedPerm_exterior (a:V×Bool) (x:FiniteHomotopyClass R (K:=K))
    (p:GeneratorPlacement (ProbeVertex V)) (v:V) (b:Bool) (hp:p.color=.inr (v,b)) :
    classGeneratorArray R (probeSignedPerm Q hn a x) p=classGeneratorArray R x p := by
  have h:Sum.inl a.1≠p.color:=by rw [hp]; exact Sum.inl_ne_inr
  unfold probeSignedPerm
  split_ifs
  · exact classPositiveTwist_exterior R x _ p h
  · exact classNegativeTwist_exterior R x _ p h

lemma probeWordPerm_exterior (w:List (V×Bool)) (x:FiniteHomotopyClass R (K:=K))
    (p:GeneratorPlacement (ProbeVertex V)) (v:V) (b:Bool) (hp:p.color=.inr (v,b)) :
    classGeneratorArray R (probeWordPerm Q hn w x) p=classGeneratorArray R x p := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    change classGeneratorArray R (probeSignedPerm Q hn a _) p=_
    rw [probeSignedPerm_exterior Q hn a _ p v b hp,ih]

lemma probeWordPerm_exterior_level (w:List (V×Bool)) (x:FiniteHomotopyClass R (K:=K))
    (v:V) (b:Bool) (d:ℤ) :
    classLevelArray R (probeWordPerm Q hn w x) (.inr (v,b),d)=classLevelArray R x (.inr (v,b),d) := by
  apply finsupp_mapDomain_fiber
  intro p hp
  exact probeWordPerm_exterior Q hn w x p v b (congrArg Prod.fst hp)

lemma probeOrbit_exterior (w:List (V×Bool)) (α β:V) (b c:Bool) (d:ℤ) :
    classLevelArray R (probeOrbit Q (K:=K) hn w α b) (.inr (β,c),d)=
      if α=β ∧ b=c ∧ d=0 then 1 else 0 := by
  rw [probeOrbit,probeWordPerm_exterior_level,classLevelArray_initial]
  simp only [Sum.inr.injEq,Prod.mk.injEq,and_assoc]

lemma probeOrbit_absent (w:List (V×Bool)) (α β:V) (b c:Bool) (hbc:b≠c) :
    ∀i,((minimalClassModel R (probeOrbit Q (K:=K) hn w α b)).complex.placement i).color≠.inr (β,c) := by
  intro i hi
  let E:=minimalClassModel R (probeOrbit Q (K:=K) hn w α b)
  let d:ℤ:=(E.complex.placement i).level
  have hz:classLevelArray R (probeOrbit Q (K:=K) hn w α b) (.inr (β,c),d)=0:=by
    rw [probeOrbit_exterior]
    simp only [hbc,and_false,false_and,ite_false]
  rw [← minimalClassModel_class R (probeOrbit Q (K:=K) hn w α b),
    classLevelArray_of_minimal R _ (minimalClassModel_minimal R _),levelArray_apply] at hz
  have hh:Nonempty {j:E.Index | (E.complex.placement j).color=.inr (β,c) ∧
      (E.complex.placement j).level=d}:=⟨⟨i,hi,rfl⟩⟩
  have hp:=Nat.card_pos (α:={j:E.Index | (E.complex.placement j).color=.inr (β,c) ∧
      (E.complex.placement j).level=d})
  have :0<Nat.card {j:E.Index | (E.complex.placement j).color=.inr (β,c) ∧
      (E.complex.placement j).level=d}:=hp
  change Nat.card {j:E.Index | (E.complex.placement j).color=.inr (β,c) ∧
      (E.complex.placement j).level=d}=0 at hz
  omega

lemma probeSignedPerm_swap (a:V×Bool) (x:FiniteHomotopyClass R (K:=K)) :
    (probeSwapIso Q).classMap (probeSignedPerm Q hn a x)=
      probeSignedPerm Q hn a ((probeSwapIso Q).classMap x) := by
  have hp:∀z:FiniteHomotopyClass R (K:=K),
      (probeSwapIso Q).classMap (classTwistPerm R hnR (.inl a.1) z)=
      classTwistPerm R hnR (.inl a.1) ((probeSwapIso Q).classMap z):=
    (probeSwapIso Q).classMap_positiveTwist (.inl a.1)
  unfold probeSignedPerm
  split_ifs
  · exact hp x
  · apply (classTwistPerm R hnR (.inl a.1)).injective
    rw [← hp,Equiv.apply_symm_apply,Equiv.apply_symm_apply]

lemma probeWordPerm_swap (w:List (V×Bool)) (x:FiniteHomotopyClass R (K:=K)) :
    (probeSwapIso Q).classMap (probeWordPerm Q hn w x)=
      probeWordPerm Q hn w ((probeSwapIso Q).classMap x) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    change (probeSwapIso Q).classMap (probeSignedPerm Q hn a _)=probeSignedPerm Q hn a _
    rw [probeSignedPerm_swap,ih]

lemma probeOrbit_swap (w:List (V×Bool)) (α:V) (b:Bool) :
    (probeSwapIso Q).classMap (probeOrbit Q (K:=K) hn w α b)=probeOrbit Q (K:=K) hn w α (!b) := by
  rw [probeOrbit,probeWordPerm_swap,Iso.classMap_initial]
  rfl

lemma probeOrbit_level_swap (w:List (V×Bool)) (α β:V) (b:Bool) (d:ℤ) :
    classLevelArray R (probeOrbit Q (K:=K) hn w α (!b)) (.inl β,d)=
      classLevelArray R (probeOrbit Q (K:=K) hn w α b) (.inl β,d) := by
  rw [← probeOrbit_swap]
  exact (probeSwapIso Q).classMap_levelArray _ (.inl β) d

end Zigzag.BasedComplex
end HarmonicArtin.ReversibleQuiver

end OAI
