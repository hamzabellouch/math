import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.PositiveComponentPositive
import OAI.Topology.ArtinGroups.Harmonic.PeakSupport

namespace OAI

namespace HarmonicArtin
open _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

omit [Fintype S] [LinearOrder S] in
lemma framedCartan_neg_of_label_ne_two (s t:S) (hst:s≠t) (hm:M s t≠2) :
    framedCartan M (.inl s) (.inl t)<0 := by
  simp only [framedCartan,hst,↓reduceIte]
  split_ifs with hz
  · norm_num
  · have hn:2<M s t:=by have h:=M.off_diagonal s t hst;omega
    have hr:(2:ℝ)<M s t:=by exact_mod_cast hn
    have hp:0<(M s t:ℝ):=by linarith
    have hc:0<Real.cos (Real.pi/(M s t:ℝ)):=by
      apply Real.cos_pos_of_mem_Ioo
      constructor
      · have h:=div_pos Real.pi_pos hp
        linarith [Real.pi_pos]
      · apply (div_lt_iff₀ hp).mpr
        nlinarith [Real.pi_pos]
    nlinarith

lemma sourceCosetVector_positive_neighbor (P:Deligne M) (k:ℤ) (i:S) (hi:i∈P.val.1)
    (j:S⊕Unit) (hij:framedCartan M (.inl i) j<0)
    (hj:0<sourceCosetVector M P k j) : 0<sourceCosetVector M P k (.inl i) := by
  apply harmonic_positive_neighbor_at (framedCartan M) (framedCartan_off M)
    (sourceCosetVector M P k) (sourceCosetVector_nonneg M P k) _ hij hj
  exact (sourceCosetVector_harmonic M P k ⟨.inl i,⟨i,hi,rfl⟩⟩).ge

lemma sourcePeak_neighbor (P:Deligne M) (i j:S) (hi:i∈P.val.1) (hj:j∈P.val.1)
    (hij:framedCartan M (.inl i) (.inl j)<0) : sourcePeak M P i=sourcePeak M P j := by
  apply le_antisymm
  · exact sourcePeak_bound M P j _ (ne_of_gt
      (sourceCosetVector_positive_neighbor M P _ j hj (.inl i)
        (by rwa [framedCartan_symm]) (sourcePeak_positive M P i hi)))
  · exact sourcePeak_bound M P i _ (ne_of_gt
      (sourceCosetVector_positive_neighbor M P _ i hi (.inl j) hij (sourcePeak_positive M P j hj)))

def sourceTypeComponent (P:Deligne M) (i:S) (hi:i∈P.val.1) : Set S :=
  {j | ∃hj:j∈P.val.1,Relation.ReflTransGen
    (fun a b:P.val.1=>framedCartan M (.inl a.val) (.inl b.val)<0) ⟨i,hi⟩ ⟨j,hj⟩}

omit [Fintype S] [LinearOrder S] in
lemma sourceTypeComponent_self (P:Deligne M) (i:S) (hi:i∈P.val.1) :
    i∈sourceTypeComponent M P i hi := ⟨hi,.refl⟩

omit [Fintype S] [LinearOrder S] in
lemma sourceTypeComponent_subset (P:Deligne M) (i:S) (hi:i∈P.val.1) :
    sourceTypeComponent M P i hi⊆P.val.1 := fun _ h=>h.choose

lemma sourceTypeComponent_peak (P:Deligne M) (i:S) (hi:i∈P.val.1)
    (j:S) (hj:j∈sourceTypeComponent M P i hi) : sourcePeak M P j=sourcePeak M P i := by
  obtain ⟨hj,h⟩:=hj
  have hgen:∀a:P.val.1,Relation.ReflTransGen
      (fun a b:P.val.1=>framedCartan M (.inl a.val) (.inl b.val)<0) ⟨i,hi⟩ a →
      sourcePeak M P a=sourcePeak M P i:=by
    intro a ha
    induction ha with
    | refl => rfl
    | @tail b c _ hbc ih => exact (sourcePeak_neighbor M P c b c.property b.property
        (by rwa [framedCartan_symm])).trans ih
  exact hgen ⟨j,hj⟩ h

omit [Fintype S] [LinearOrder S] in
lemma sourceTypeComponent_closed (P:Deligne M) (i:S) (hi:i∈P.val.1)
    (j:S) (hj:j∈sourceTypeComponent M P i hi) (k:S) (hk:k∈P.val.1)
    (hjk:framedCartan M (.inl j) (.inl k)<0) : k∈sourceTypeComponent M P i hi := by
  obtain ⟨hj,h⟩:=hj
  exact ⟨hk,h.tail hjk⟩

omit [Fintype S] [LinearOrder S] in
lemma sourceTypeComponent_commutes (P:Deligne M) (i:S) (hi:i∈P.val.1)
    (j:S) (hj:j∈sourceTypeComponent M P i hi) (k:S)
    (hk:k∈P.val.1\sourceTypeComponent M P i hi) : M j k=2 := by
  by_contra hn
  exact hk.2 (sourceTypeComponent_closed M P i hi j hj k hk.1
    (framedCartan_neg_of_label_ne_two M j k (by rintro rfl;exact hk.2 hj) hn))

lemma sourceTypeComponent_positiveComponent (P:Deligne M) (i:S) (hi:i∈P.val.1)
    (j:S) (hj:j∈sourceTypeComponent M P i hi) :
    sourcePositiveComponent M (sourceCosetVector M P (sourcePeak M P i)) (.inl j)=
      sourcePositiveComponent M (sourceCosetVector M P (sourcePeak M P i)) (.inl i) := by
  apply sourcePositiveComponent_eq M _ _ _
    (sourcePositiveComponent_spec M _ _ (sourcePeak_positive M P i hi))
  obtain ⟨hj,h⟩:=hj
  have hgen:∀a:P.val.1,Relation.ReflTransGen
      (fun a b:P.val.1=>framedCartan M (.inl a.val) (.inl b.val)<0) ⟨i,hi⟩ a →
      (.inl a.val:S⊕Unit)∈sourcePositiveComponent M (sourceCosetVector M P (sourcePeak M P i)) (.inl i):=by
    intro a ha
    induction ha with
    | refl => exact .refl
    | @tail b c h hbc ih =>
      have hb:sourcePeak M P b=sourcePeak M P i:=sourceTypeComponent_peak M P i hi b ⟨b.property,h⟩
      have hc:=sourceTypeComponent_peak M P i hi c ⟨c.property,h.tail hbc⟩
      exact ih.tail ⟨by rw [←hb];exact sourcePeak_positive M P b b.property,
        hbc,by rw [←hc];exact sourcePeak_positive M P c c.property⟩
  exact hgen ⟨j,hj⟩ h

lemma sourceTypeComponent_sign (P:Deligne M) (i:S) (hi:i∈P.val.1)
    (j:S) (hj:j∈sourceTypeComponent M P i hi) :
    sourceCosetSign M P (sourcePeak M P i) (.inl j)=
      sourceCosetSign M P (sourcePeak M P i) (.inl i) := by
  have he:=sourceTypeComponent_peak M P i hi j hj
  have hjp:=sourcePeak_positive M P j (sourceTypeComponent_subset M P i hi hj)
  rw [he] at hjp
  have hn:SourceNullSign M (fun d=>sourceCosetVector M P d) (sourcePeak M P i) (.inl j) ↔
      SourceNullSign M (fun d=>sourceCosetVector M P d) (sourcePeak M P i) (.inl i):=by
    unfold SourceNullSign
    rw [sourceTypeComponent_positiveComponent M P i hi j hj]
  change sourceSignAt M _ _ (.inl j)=sourceSignAt M _ _ (.inl i)
  unfold sourceSignAt
  rw [ite_eq_right (ne_of_gt hjp),ite_eq_right (ne_of_gt (sourcePeak_positive M P i hi))]
  by_cases hjn:SourceNullSign M (fun d=>sourceCosetVector M P d) (sourcePeak M P i) (.inl j)
  · rw [ite_eq_left hjn,ite_eq_left (hn.mp hjn)]
  · rw [ite_eq_right hjn,ite_eq_right (fun membership=>hjn (hn.mpr membership))]

lemma sourceBlock_above_boundary (P:Deligne M) (B:Set S) (hB:B⊆P.val.1) (q:ℕ)
    (hq:∀i∈B,sourcePeak M P i=q) (v:S⊕Unit)
    (hv:∃i∈B,framedCartan M (.inl i) v<0) (d:ℕ) (hd:q<d) :
    sourceCosetVector M P d v=0 := by
  obtain ⟨i,hi,hiv⟩:=hv
  by_contra hn
  have hp:=sourceCosetVector_positive_neighbor M P d i (hB hi) v hiv
    (lt_of_le_of_ne (sourceCosetVector_nonneg M P d v) (Ne.symm hn))
  have hz:=sourcePeak_above M P i (by rwa [hq i hi])
  exact (ne_of_gt hp) hz

lemma sourcePositiveComponent_type_neighbor (P:Deligne M) (q:ℕ) (i:S⊕Unit)
    (hi:0<sourceCosetVector M P q i) (j:S⊕Unit)
    (hj:j∈sourcePositiveComponent M (sourceCosetVector M P q) i) (k:S) (hk:k∈P.val.1)
    (hjk:framedCartan M j (.inl k)<0) :
    (.inl k:S⊕Unit)∈sourcePositiveComponent M (sourceCosetVector M P q) i := by
  have hp:=sourcePositiveComponent_positive M _ i hi j hj
  have hkp:=sourceCosetVector_positive_neighbor M P q k hk j (by rwa [framedCartan_symm]) hp
  exact hj.tail ⟨hp,hjk,hkp⟩

lemma sourcePositiveBlock_commutes (P:Deligne M) (q:ℕ) (i:S⊕Unit)
    (hi:0<sourceCosetVector M P q i) (j k:S) (_hj:j∈P.val.1)
    (hjI:(.inl j:S⊕Unit)∈sourcePositiveComponent M (sourceCosetVector M P q) i)
    (hk:k∈P.val.1) (hkI:(.inl k:S⊕Unit)∉sourcePositiveComponent M (sourceCosetVector M P q) i) :
    M j k=2 := by
  by_contra hn
  exact hkI (sourcePositiveComponent_type_neighbor M P q i hi (.inl j) hjI k hk
    (framedCartan_neg_of_label_ne_two M j k (by rintro rfl;exact hkI hjI) hn))

end HarmonicArtin

end OAI
