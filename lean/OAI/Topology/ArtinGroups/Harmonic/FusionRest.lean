import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.StringAdjacent
import OAI.Topology.ArtinGroups.Harmonic.FusionVertex

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver

attribute [local instance] Classical.propDecidable
variable {E V : Type} [Fintype E] [DecidableEq E] (m:E → ℕ) (e:E)

abbrev FusionRest := {f:E // f ≠ e}
abbrev restLabel (L:FusionLabel m) : FusionLabel (fun f:FusionRest e => m f) := fun f => L f

def labelSplit : FusionLabel m ≃ FusionLabel (fun f:FusionRest e => m f) × StringLabel (m e) :=
  (Equiv.piSplitAt e (fun f => StringLabel (m f))).trans (Equiv.prodComm _ _)

omit [Fintype E] in
@[simp] lemma labelSplit_apply (L:FusionLabel m) : labelSplit m e L = (restLabel m e L,L e) := rfl

omit [Fintype E] in
lemma label_eq_iff (L L':FusionLabel m) :
    L=L' ↔ restLabel m e L = restLabel m e L' ∧ L e=L' e := by
  rw [← (labelSplit m e).injective.eq_iff]
  simp only [labelSplit_apply,Prod.mk.injEq]

omit [Fintype E] [DecidableEq E] in
lemma restLabel_eq_iff (L L':FusionLabel m) :
    restLabel m e L = restLabel m e L' ↔ ∀ f, f ≠ e → L f=L' f := by
  constructor
  · intro h f hf; exact congrFun h ⟨f,hf⟩
  · intro h; funext f; exact h f f.property

noncomputable def FusionEdge.usesFactor (d:FusionEdge E) : Bool :=
  match d with
  | .units _ => false
  | .string f => decide (f=e)

noncomputable def FusionEdge.removeFactor (d:FusionEdge E) : FusionEdge (FusionRest e) :=
  match d with
  | .units n => .units n
  | .string f => if h:f=e then .units 1 else .string ⟨f,h⟩

lemma stringMultiplicity_eq_ite (n:ℕ) (a b:StringLabel n) :
    stringMultiplicity n a b = if stringAdjacent n a b then 1 else 0 := by
  by_cases h₁:a.val+1=b.val
  · have h₂ : ¬ b.val+1=a.val := by omega
    simp [stringMultiplicity,stringAdjacent,h₁,h₂]
  · by_cases h₂:b.val+1=a.val <;> simp [stringMultiplicity,stringAdjacent,h₁,h₂]

lemma factorMultiplicity_split_other (f:E) (hf:f≠e) (L L':FusionLabel m) :
    factorMultiplicity m f L L' =
      if L e=L' e then
        factorMultiplicity (fun g:FusionRest e => m g) ⟨f,hf⟩ (restLabel m e L) (restLabel m e L')
      else 0 := by
  have hh : (∀ g, g ≠ f → L g=L' g) ↔
      L e=L' e ∧ ∀ g:FusionRest e, g ≠ ⟨f,hf⟩ → L g=L' g := by
    constructor
    · intro h; refine ⟨h e hf.symm,fun g hg => h g ?_⟩
      intro hgf; exact hg (Subtype.ext hgf)
    · rintro ⟨he,h⟩ g hg
      by_cases hge:g=e
      · subst g; exact he
      · exact h ⟨g,hge⟩ (fun heq => hg (congrArg Subtype.val heq))
  unfold factorMultiplicity
  simp only [hh,restLabel]
  split_ifs <;> simp_all

lemma FusionEdge.multiplicity_split (d:FusionEdge E) (L L':FusionLabel m) :
    d.multiplicity m L L' =
      if (if d.usesFactor e then stringAdjacent (m e) (L e) (L' e) else L e=L' e) then
        (d.removeFactor e).multiplicity (fun f:FusionRest e => m f) (restLabel m e L) (restLabel m e L')
      else 0 := by
  cases d with
  | units n =>
    simp only [FusionEdge.multiplicity,FusionEdge.usesFactor,FusionEdge.removeFactor,
      Bool.false_eq_true,↓reduceIte,label_eq_iff m e]
    split_ifs <;> simp_all
  | string f =>
    by_cases hf:f=e
    · subst f
      simp only [FusionEdge.multiplicity,FusionEdge.usesFactor,FusionEdge.removeFactor,
        decide_true,↓reduceIte,factorMultiplicity,← restLabel_eq_iff m e,stringMultiplicity_eq_ite]
      split_ifs <;> rfl
    · simp only [FusionEdge.multiplicity,FusionEdge.usesFactor,FusionEdge.removeFactor,
        hf,decide_false,↓reduceIte,Bool.false_eq_true]
      exact factorMultiplicity_split_other m e f hf L L'

def fusionVertexSplit : FusionVertex (V:=V) m ≃
    FusionVertex (V:=V) (fun f:FusionRest e => m f) × StringLabel (m e) where
  toFun α := ((α.1,restLabel m e α.2),α.2 e)
  invFun α := (α.1.1,(labelSplit m e).symm (α.1.2,α.2))
  left_inv α := Prod.ext rfl ((labelSplit m e).symm_apply_apply α.2)
  right_inv α := by
    obtain ⟨⟨v,L⟩,a⟩ := α
    have h := (labelSplit m e).apply_symm_apply (L,a)
    change ((v,restLabel m e ((labelSplit m e).symm (L,a))),
      ((labelSplit m e).symm (L,a)) e) = ((v,L),a)
    change (restLabel m e ((labelSplit m e).symm (L,a)),
      ((labelSplit m e).symm (L,a)) e) = (L,a) at h
    exact congrArg (fun z : FusionLabel (fun f:FusionRest e => m f) × StringLabel (m e) =>
      ((v,z.1),z.2)) h

end HarmonicArtin

end OAI
