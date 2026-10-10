import Mathlib
import OAI.Topology.ArtinGroups.Complexes.InitialProjective
import OAI.Topology.ArtinGroups.Complexes.HomStep
import OAI.Topology.ArtinGroups.Complexes.HomPath

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V]

lemma offDiagonal_vertex_zero {s t:V} {x:Q.Zigzag K}
    (hl:vertexId Q s*x=x) (hr:x*vertexId Q t=x) (hst:s≠t) : x.vertex=0 := by
  funext v
  by_contra hv
  have h:=coordinates_corner Q hl hr (p:=.inl v) hv
  exact hst (h.1.symm.trans h.2)

lemma offDiagonal_token_zero {s t:V} {x:Q.Zigzag K}
    (hl:vertexId Q s*x=x) (hr:x*vertexId Q t=x) (hst:s≠t) : x.token=0 := by
  funext v
  by_contra hv
  have h:=coordinates_corner Q hl hr (p:=.inr (.inr v)) hv
  exact hst (h.1.symm.trans h.2)

lemma offDiagonal_radical_mul_zero {s t u:V} {x y:Q.Zigzag K}
    (hl:vertexId Q s*x=x) (hr:x*vertexId Q t=x) (hst:s≠t)
    (hy:y.vertex=0) (hyr:y*vertexId Q u=y) (hsu:s≠u) : x*y=0 := by
  have hv:=offDiagonal_vertex_zero Q hl hr hst
  have ht: (x*y).token=0 := offDiagonal_token_zero Q
    (by rw [← mul_assoc,hl]) (by rw [mul_assoc,hyr]) hsu
  apply Zigzag.ext
  · simp only [vertex_mul,hv,MulZeroClass.zero_mul,vertex_zero]
  · ext a
    simp only [arrow_mul,hv,hy,leftScale,rightScale,Pi.add_apply,Pi.zero_apply,
      MulZeroClass.zero_mul,MulZeroClass.mul_zero,add_zero,arrow_zero]
  · exact ht

namespace BasedComplex
variable {I:Type*} [Fintype I]

lemma absentProjective_homDifferential_zero (E:BasedComplex Q (K:=K) I)
    (hE:E.IsMinimal Q) (α:V) (ha:∀i,(E.placement i).color≠α)
    (n v:ℤ) {f:Matrix PUnit.{1} I (Q.Zigzag K)}
    (hf:f∈homSpace Q ((initialProjective Q α : BasedComplex Q (K:=K) PUnit.{1})) E n v) :
    homDifferential Q ((initialProjective Q α : BasedComplex Q (K:=K) PUnit.{1})) E n f=0 := by
  have hm:f*E.differential=0 := by
    apply Matrix.ext
    intro i k
    change (∑j,f i j*E.differential j k)=0
    apply Finset.sum_eq_zero
    intro j _
    exact offDiagonal_radical_mul_zero Q (hf.1.1 i j) (hf.1.2 i j)
      (Ne.symm (ha j)) (hE j k) (E.entries.2 j k) (Ne.symm (ha k))
  change (0:Matrix PUnit.{1} PUnit.{1} (Q.Zigzag K))*f-cochainSign (K:=K) n • (f*E.differential)=0
  rw [hm,Matrix.zero_mul,smul_zero,sub_zero]

lemma absentProjective_homBoundaries_bot (E:BasedComplex Q (K:=K) I)
    (hE:E.IsMinimal Q) (α:V) (ha:∀i,(E.placement i).color≠α) (n v:ℤ) :
    homBoundaries Q ((initialProjective Q α : BasedComplex Q (K:=K) PUnit.{1})) E n v=⊥ := by
  apply le_antisymm _ bot_le
  rintro x ⟨f,hf,rfl⟩
  exact absentProjective_homDifferential_zero Q E hE α ha (n-1) v hf

variable [Fintype V] [DecidableEq A]

lemma absentProjective_homDimension (E:BasedComplex Q (K:=K) I)
    (hE:E.IsMinimal Q) (α:V) (ha:∀i,(E.placement i).color≠α) (n v:ℤ) :
    homDimension Q ((initialProjective Q α : BasedComplex Q (K:=K) PUnit.{1})) E n v=
      Nat.card (HomPath Q ((initialProjective Q α : BasedComplex Q (K:=K) PUnit.{1})) E n v) := by
  have h:=hom_exact_dimension Q ((initialProjective Q α : BasedComplex Q (K:=K) PUnit.{1})) E n v
  rw [absentProjective_homBoundaries_bot Q E hE α ha,
    absentProjective_homBoundaries_bot Q E hE α ha,finrank_bot,
    add_zero,add_zero,homSpace_finrank] at h
  exact h

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
