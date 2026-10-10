import Mathlib
import OAI.Topology.ArtinGroups.Quivers.ProbeSwapIso

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A:Type} {K:Type*} [Field K] [Fintype V] [Fintype A]
  (Q:ReversibleQuiver V A)
attribute [local instance] Classical.decEq Classical.propDecidable

lemma classHomDimension_dual [DecidableEq V] (x y:FiniteHomotopyClass Q (K:=K)) (n v:ℤ) :
    classHomDimension Q n v x y=classHomDimension Q (-n) (2-v) y x := by
  induction x using Quotient.inductionOn with | _ E =>
    induction y using Quotient.inductionOn with | _ F =>
      exact homDimension_dual Q E.complex F.complex n v

local notation "R" => probeQuiver Q

lemma probeHomDimension_generatorArray {I:Type} [Fintype I]
    (E:BasedComplex R (K:=K) I) (hE:E.IsMinimal R)
    (α:V) (b:Bool) (ha:∀i,(E.placement i).color≠.inr (α,b)) (n v:ℤ) :
    homDimension R ((initialProjective R (.inr (α,b)) : BasedComplex R (K:=K) PUnit.{1})) E n v=
      E.generatorArray R ⟨.inl α,n,v-1⟩ := by
  rw [probeHomDimension Q E hE α b ha,generatorArray_apply]
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight fun i => by
    cases E.placement i
    simp only [GeneratorPlacement.mk.injEq]

lemma probeClassHomDimension_generatorArray (x:FiniteHomotopyClass R (K:=K))
    (α:V) (b:Bool)
    (ha:∀i,((minimalClassModel R x).complex.placement i).color≠.inr (α,b)) (n v:ℤ) :
    classHomDimension R n v (initialClass R (.inr (α,b))) x=
      classGeneratorArray R x ⟨.inl α,n,v-1⟩ := by
  rw [← minimalClassModel_class R x, classGeneratorArray_of_minimal R _
    (minimalClassModel_minimal R x)]
  exact probeHomDimension_generatorArray Q _ (minimalClassModel_minimal R x) α b ha n v

variable (hn:∀a,Q.source a≠Q.target a)

lemma probeWordPerm_append (w z:List (V×Bool)) :
    probeWordPerm Q (K:=K) hn (w++z)=probeWordPerm Q hn w*probeWordPerm Q hn z := by
  induction w with
  | nil => exact (_root_.one_mul _).symm
  | cons a w ih => simp only [List.cons_append,probeWordPerm,ih,_root_.mul_assoc]

lemma probeSignedPerm_inverse (a:V×Bool) :
    probeSignedPerm Q (K:=K) hn (a.1,!a.2)=(probeSignedPerm Q hn a)⁻¹ := by
  cases a with | mk v b => cases b <;> rfl

lemma probeWordPerm_inverse (w:List (V×Bool)) :
    probeWordPerm Q (K:=K) hn (w.reverse.map fun a=>(a.1,!a.2))=(probeWordPerm Q hn w)⁻¹ := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    simp only [List.reverse_cons,List.map_append,List.map_cons,List.map_nil,
      probeWordPerm_append,probeWordPerm,_root_.mul_one,ih,
      probeSignedPerm_inverse,mul_inv_rev]

lemma probeOrbit_generator_dual (w:List (V×Bool)) (α β:V) (n u:ℤ) :
    classGeneratorArray R (probeOrbit Q (K:=K) hn w α false) ⟨.inl β,n,u⟩=
      classGeneratorArray R
        (probeOrbit Q (K:=K) hn (w.reverse.map fun a=>(a.1,!a.2)) β true) ⟨.inl α,-n,-u⟩ := by
  have h₁:=probeClassHomDimension_generatorArray Q (probeOrbit Q (K:=K) hn w α false) β true
    (probeOrbit_absent Q (K:=K) hn w α β false true (by decide)) n (u+1)
  have h₂:=probeClassHomDimension_generatorArray Q
    (probeOrbit Q (K:=K) hn (w.reverse.map fun a=>(a.1,!a.2)) β true) α false
    (probeOrbit_absent Q (K:=K) hn _ β α true false (by decide)) (-n) (1-u)
  have hu:(u+1)-1=u:=by omega
  have hv:(1-u)-1= -u:=by omega
  rw [hu] at h₁
  rw [hv] at h₂
  rw [← h₁,← h₂]
  have hd:=classHomDimension_dual R (K:=K) (initialClass R (.inr (β,true)))
    (probeOrbit Q (K:=K) hn w α false) n (u+1)
  apply hd.trans
  have hsh:2-(u+1)=1-u:=by omega
  rw [hsh]
  unfold probeOrbit
  rw [probeWordPerm_inverse]
  have he:=probeWordPerm_homDimension Q (K:=K) hn w
    (initialClass R (.inr (α,false)))
    ((probeWordPerm Q hn w).symm (initialClass R (.inr (β,true)))) (-n) (1-u)
  rw [Equiv.apply_symm_apply] at he
  exact he

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
