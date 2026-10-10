import Mathlib

namespace OAI

namespace HarmonicArtin
open scoped unitInterval
open Topology

attribute [local instance] Classical.propDecidable
universe u v
variable {X:Type u} {Y:Type v} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y]

abbrev EarlyDelay (δ:C(X,I)) := {p:I×X // p.1≤δ p.2}

noncomputable def earlyDelayMap (δ:C(X,I)) : C(I×X,EarlyDelay δ) where
  toFun := fun p => ⟨(p.1*δ p.2,p.2),mul_le_of_le_one_left (by exact bot_le) (by exact le_top)⟩
  continuous_toFun:=Continuous.subtype_mk
    ((continuous_fst.mul (δ.continuous.comp continuous_snd)).prodMk continuous_snd) _

omit [T2Space X] in
lemma earlyDelayMap_surjective (δ:C(X,I)) : Function.Surjective (earlyDelayMap δ) := by
  rintro ⟨⟨t,x⟩,ht⟩
  by_cases hd:δ x=0
  · have h:t=0:=le_antisymm (hd ▸ ht) t.property.1
    subst t
    refine ⟨(0,x),?_⟩
    apply Subtype.ext
    simp [earlyDelayMap]
  · have hdv:(δ x).val≠0:=by intro he;apply hd;exact Subtype.ext he
    have hp:0<(δ x).val:=lt_of_le_of_ne (δ x).property.1 (Ne.symm hdv)
    let s:I:=⟨t.val/(δ x).val,div_nonneg t.property.1 hp.le,(div_le_one hp).mpr ht⟩
    refine ⟨(s,x),?_⟩
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact div_mul_cancel₀ _ hdv
    · rfl

lemma earlyDelayMap_quotient (δ:C(X,I)) : IsQuotientMap (earlyDelayMap δ) := by
  have hp:IsProperMap (earlyDelayMap δ):=
    isProperMap_of_comp_of_t2 (earlyDelayMap δ).continuous
      (continuous_snd.comp continuous_subtype_val) isProperMap_snd_of_compactSpace
  exact hp.isClosedMap.isQuotientMap (earlyDelayMap δ).continuous (earlyDelayMap_surjective δ)

noncomputable def earlyDelayValue (δ:C(X,I)) (D:C(I×X,Y)) (p:EarlyDelay δ) : Y :=
  D ((earlyDelayMap_surjective δ p).choose)

omit [T2Space X] in
lemma earlyDelayValue_map (δ:C(X,I)) (D:C(I×X,Y))
    (hD:∀x,δ x=0→∀t:I,D (t,x)=D (0,x)) (p:I×X) :
    earlyDelayValue δ D (earlyDelayMap δ p)=D p := by
  let q:=(earlyDelayMap_surjective δ (earlyDelayMap δ p)).choose
  have he:earlyDelayMap δ q=earlyDelayMap δ p:=
    (earlyDelayMap_surjective δ (earlyDelayMap δ p)).choose_spec
  have hx:q.2=p.2:=congrArg (fun z:EarlyDelay δ=>z.val.2) he
  have ht:q.1*δ q.2=p.1*δ p.2:=congrArg (fun z:EarlyDelay δ=>z.val.1) he
  change D q=D p
  change D (q.1,q.2)=D (p.1,p.2)
  rw [hx]
  by_cases hd:δ p.2=0
  · exact (hD _ hd q.1).trans (hD _ hd p.1).symm
  · have hdv:(δ p.2).val≠0:=by intro he;apply hd;exact Subtype.ext he
    have heq:q.1=p.1:=by
      apply Subtype.ext
      have h:=congrArg Subtype.val ht
      change q.1.val*(δ q.2).val=p.1.val*(δ p.2).val at h
      rw [hx] at h
      exact mul_right_cancel₀ hdv h
    rw [heq]

noncomputable def earlyDelayContinuous (δ:C(X,I)) (D:C(I×X,Y))
    (hD:∀x,δ x=0→∀t:I,D (t,x)=D (0,x)) : C(EarlyDelay δ,Y) where
  toFun:=earlyDelayValue δ D
  continuous_toFun:=by
    apply (earlyDelayMap_quotient δ).continuous_iff.mpr
    have he:(earlyDelayValue δ D) ∘ earlyDelayMap δ=D:=by
      funext p
      exact earlyDelayValue_map δ D hD p
    rw [he]
    exact D.continuous

end HarmonicArtin

end OAI
