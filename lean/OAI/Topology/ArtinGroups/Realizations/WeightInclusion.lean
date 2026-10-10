import Mathlib
import OAI.Topology.ArtinGroups.Realizations.ConeWeights

namespace OAI

namespace HarmonicArtin
open scoped BigOperators unitInterval
open Simplicial CategoryTheory Opposite

attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {P:Type u} [PartialOrder P]

noncomputable def weightInclusion (A:Set P) : A→oP :=⟨Subtype.val,fun _ _ h=>h⟩

noncomputable def weightRestrict (A:Set P) (w:OrderWeights P) (hw:∀p∈w.weights.support,p∈A) : OrderWeights A where
  weights:=w.weights.subtypeDomain (·∈A)
  nonneg p:=w.nonneg p.val
  total:=by
    exact (Finsupp.sum_subtypeDomain_index (h := fun (_:P) (a:ℝ)=>a) hw).trans w.total
  chain:=by
    intro p hp q hq
    apply w.chain p.val _ q.val _
    · rw [Finsupp.mem_support_iff] at hp ⊢
      exact hp
    · rw [Finsupp.mem_support_iff] at hq ⊢
      exact hq

lemma weightRestrict_apply (A:Set P) (w:OrderWeights P) (hw:∀p∈w.weights.support,p∈A) (p:A) :
    (weightRestrict A w hw).weights p=w.weights p.val :=rfl

lemma weightRestrict_map (A:Set P) (w:OrderWeights P) (hw:∀p∈w.weights.support,p∈A) :
    weightMap (weightInclusion A) (weightRestrict A w hw)=w := by
  apply OrderWeights.ext
  ext p
  by_cases hp:p∈A
  · exact weightMap_apply_embedding (weightInclusion A) Subtype.val_injective _ ⟨p,hp⟩
  · have h₁:p∉(weightMap (weightInclusion A) (weightRestrict A w hw)).weights.support:=by
      rw [weightMap_support_embedding _ Subtype.val_injective]
      rintro hx
      obtain ⟨q,_,he⟩:=Finset.mem_image.mp hx
      exact hp (he ▸ q.property)
    have h₂:p∉w.weights.support:=fun h=>hp (hw _ h)
    exact (Finsupp.notMem_support_iff.mp h₁).trans (Finsupp.notMem_support_iff.mp h₂).symm

lemma weight_le_one (w:OrderWeights P) (p:P) : w.weights p≤1 := by
  by_cases hp:p∈w.weights.support
  · rw [←w.total]
    exact Finset.single_le_sum (fun q _=>w.nonneg q) hp
  · rw [Finsupp.notMem_support_iff.mp hp]
    norm_num

noncomputable def weightTime (v:P) (w:OrderWeights P) : I :=⟨w.weights v,w.nonneg v,weight_le_one w v⟩

noncomputable def weightVertex (v:P) : OrderWeights P where
  weights:=Finsupp.single v 1
  nonneg p:=by simp only [Finsupp.single_apply];split_ifs <;> norm_num
  total:=by simp
  chain:=by
    intro p hp q hq
    have hpv:p=v:=Finset.mem_singleton.mp (Finsupp.support_single_subset hp)
    have hqv:q=v:=Finset.mem_singleton.mp (Finsupp.support_single_subset hq)
    subst p;subst q;exact Or.inl le_rfl

lemma coneWeights_one_vertex {Q:Type*} [PartialOrder Q] (f:Q→oP) (v:P) (hv:∀q,f q≤v ∨ v≤f q)
    (w:OrderWeights Q) : coneWeights f v hv 1 w=weightVertex v := by
  apply OrderWeights.ext
  simp [coneWeights,weightVertex]

lemma weight_eq_vertex_of_one (w:OrderWeights P) (v:P) (hv:w.weights v=1) : w=weightVertex v := by
  have hvS:v∈w.weights.support:=Finsupp.mem_support_iff.mpr (hv ▸ one_ne_zero)
  have hsum:∑p∈w.weights.support.erase v,w.weights p=0:=by
    have ht:=w.total
    change (∑p∈w.weights.support,w.weights p)=1 at ht
    rw [←Finset.add_sum_erase _ _ hvS,hv] at ht
    linarith
  apply OrderWeights.ext
  ext p
  by_cases hp:p=v
  · subst p;simp [weightVertex,hv]
  · have he:w.weights p=0:=by
      by_cases hps:p∈w.weights.support
      · have hm:p∈w.weights.support.erase v:=Finset.mem_erase.mpr ⟨hp,hps⟩
        have hl:=Finset.single_le_sum (fun q _=>w.nonneg q) hm
        rw [hsum] at hl
        exact le_antisymm hl (w.nonneg p)
      · exact Finsupp.notMem_support_iff.mp hps
    simp [weightVertex,he,Ne.symm hp]

noncomputable def weightDelete (v:P) (w:OrderWeights P) (hv:w.weights v<1) : OrderWeights P where
  weights:=(1-w.weights v)⁻¹ • w.weights.erase v
  nonneg p:=by
    change 0≤ (1-w.weights v)⁻¹ * (w.weights.erase v) p
    apply mul_nonneg (inv_nonneg.mpr (sub_nonneg.mpr hv.le))
    by_cases hp:p=v
    · subst p;simp
    · rw [Finsupp.erase_ne hp]
      exact w.nonneg p
  total:=by
    rw [Finsupp.sum_smul_index (by intros;rfl)]
    change (∑p∈(w.weights.erase v).support,(1-w.weights v)⁻¹*(w.weights.erase v) p)=1
    rw [←Finset.mul_sum]
    have he:(w.weights.erase v).sum (fun _ a=>a)=1-w.weights v:=by
      have hh:=congrArg (fun z:P→₀ℝ=>z.sum (fun _ a=>a)) (Finsupp.single_add_erase v w.weights)
      rw [Finsupp.sum_add_index (by intros;rfl) (by intros;rfl),Finsupp.sum_single_index (by rfl),w.total] at hh
      linarith
    change (1-w.weights v)⁻¹*((w.weights.erase v).sum (fun _ a=>a))=1
    rw [he,inv_mul_cancel₀ (ne_of_gt (sub_pos.mpr hv))]
  chain:=by
    intro p hp q hq
    apply w.chain p _ q _
    · have ht:=Finsupp.support_smul hp
      rw [Finsupp.support_erase] at ht
      exact (Finset.mem_erase.mp ht).2
    · have ht:=Finsupp.support_smul hq
      rw [Finsupp.support_erase] at ht
      exact (Finset.mem_erase.mp ht).2

lemma weightDelete_apply (v:P) (w:OrderWeights P) (hv:w.weights v<1) (p:P) :
    (weightDelete v w hv).weights p=(1-w.weights v)⁻¹*(if p=v then 0 else w.weights p) := by
  simp only [weightDelete,Finsupp.smul_apply,smul_eq_mul,Finsupp.erase_apply]

lemma weightDelete_support (v:P) (w:OrderWeights P) (hv:w.weights v<1) :
    (weightDelete v w hv).weights.support⊆w.weights.support.erase v := by
  exact Finsupp.support_smul.trans (by rw [Finsupp.support_erase])

end HarmonicArtin

end OAI
