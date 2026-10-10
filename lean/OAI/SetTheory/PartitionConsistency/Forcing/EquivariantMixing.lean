import Mathlib
import OAI.SetTheory.PartitionConsistency.Forcing.SymmetricChoice

namespace OAI

/-! ## Mixing -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w t
noncomputable section
variable {P : Type w} [Preorder P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)
variable {ι : Type t} [Small.{u} ι]

/-- Index the literal children of a small family, with no uniform bound on
the ranks of the family's members. -/
abbrev MixEntries (f : ι → S.Name) := Σ i, Edges (f i).raw

def mixTest (f : ι → S.Name) (a : ι → P) (i : S.MixEntries f) (p : P) : Prop :=
  p ≤ a i.1 ∧ S.atomic.MemF p ((f i.1).child i.2.property) (f i.1)

omit [Small.{u} ι] in
/-- Fixing the names and their activation conditions permutes every entry
of their union mixture, including all strengthenings of all activations. -/
theorem mixTest_permute (f : ι → S.Name) (a : ι → P) (H : Subgroup Γ)
    (hf : ∀ g ∈ H, ∀ i, g • f i = f i)
    (ha : ∀ g ∈ H, ∀ i, S.move g (a i) = a i) :
    ∀ g ∈ H, ∀ (i : S.MixEntries f) p, S.mixTest f a i p →
      ∃ j : S.MixEntries f, (f j.1).child j.2.property = g • (f i.1).child i.2.property ∧
        S.mixTest f a j (S.move g p) := by
  intro g hg i p hp
  have he := S.entry_permute g (f i.1) i.2
  rw [hf g hg i.1] at he
  obtain ⟨j,hj⟩ := he
  refine ⟨⟨i.1,j⟩,hj,?_,?_⟩
  · change S.move g p ≤ a i.1
    rw [← ha g hg i.1]
    exact (S.move g).monotone hp.1
  · change S.atomic.MemF (S.move g p) ((f i.1).child j.property) (f i.1)
    rw [hj]
    simpa only [hf g hg i.1] using (S.mem_symmetry g p _ (f i.1)).mp hp.2

/-- A coherent or antichain mixture. Coherence is a property proved separately;
the present construction itself is just the unrestricted union of active names. -/
def mix (f : ι → S.Name) (a : ι → P) (H : Subgroup Γ) (hH : H ∈ S.filter)
    (hf : ∀ g ∈ H, ∀ i, g • f i = f i)
    (ha : ∀ g ∈ H, ∀ i, S.move g (a i) = a i) : S.Name :=
  S.collect (fun i : S.MixEntries f => (f i.1).child i.2.property)
    (S.mixTest f a) H hH (S.mixTest_permute f a H hf ha)

theorem mix_fixed (f : ι → S.Name) (a : ι → P) (H : Subgroup Γ) (hH : H ∈ S.filter)
    (hf : ∀ g ∈ H, ∀ i, g • f i = f i)
    (ha : ∀ g ∈ H, ∀ i, S.move g (a i) = a i) (g : Γ) (hg : g ∈ H) :
    g • S.mix f a H hH hf ha = S.mix f a H hH hf ha :=
  Subtype.ext (S.collectName_fixed _ _ H (S.mixTest_permute f a H hf ha) g hg)

theorem edge_mix (f : ι → S.Name) (a : ι → P) (H : Subgroup Γ) (hH : H ∈ S.filter)
    (hf : ∀ g ∈ H, ∀ i, g • f i = f i)
    (ha : ∀ g ∈ H, ∀ i, S.move g (a i) = a i) (ν : S.Name) (p : P) :
    ZFSet.pair ν.raw (S.code p) ∈ (S.mix f a H hH hf ha).raw ↔
      ∃ i : S.MixEntries f, (f i.1).child i.2.property = ν ∧ S.mixTest f a i p := by
  change ZFSet.pair ν.raw (S.code p) ∈
    S.collectRaw (fun i : S.MixEntries f => (f i.1).child i.2.property) (S.mixTest f a) ↔ _
  rw [S.edge_collectRaw]
  constructor
  · rintro ⟨i,c,hi,hν,hc⟩
    obtain rfl := S.code_injective hc
    exact ⟨i,Name.ext hν,hi⟩
  · rintro ⟨i,hi,hR⟩
    exact ⟨i,p,hR,congrArg Name.raw hi,rfl⟩

/-- The exact regular forcing value of membership in the union mixture. -/
theorem mem_mix (f : ι → S.Name) (a : ι → P) (H : Subgroup Γ) (hH : H ∈ S.filter)
    (hf : ∀ g ∈ H, ∀ i, g • f i = f i)
    (ha : ∀ g ∈ H, ∀ i, S.move g (a i) = a i) (ν : S.Name) (p : P) :
    S.atomic.MemF p ν (S.mix f a H hH hf ha) ↔
      ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ i : ι, r ≤ a i ∧ S.atomic.MemF r ν (f i) := by
  constructor
  · intro h q hqp
    obtain ⟨r,hrq,τ,c,he,hrc,heq⟩ := S.mem_iff.mp h q hqp
    obtain ⟨i,hi,hia,hit⟩ := (S.edge_mix f a H hH hf ha τ c).mp he
    change S.atomic.MemF c ((f i.1).child i.2.property) (f i.1) at hit
    rw [hi] at hit
    exact ⟨r,hrq,i.1,hrc.trans hia,
      (S.atomic.mem_congr heq (S.atomic.eq_refl r (f i.1))).mpr (S.atomic.mem_mono hrc hit)⟩
  · intro h
    apply S.mem_iff.mpr
    intro q hqp
    obtain ⟨r,hrq,i,hria,hν⟩ := h q hqp
    obtain ⟨s,hsr,τ,c,he,hsc,heq⟩ := S.mem_iff.mp hν r le_rfl
    let j : S.MixEntries f := ⟨i,⟨(τ.raw,S.code c),he⟩⟩
    have hj : (f j.1).child j.2.property = τ := Name.ext rfl
    have ht : S.mixTest f a j s := by
      change s ≤ a i ∧ S.atomic.MemF s ((f i).child he) (f i)
      exact ⟨hsr.trans hria,S.mem_of_edge he hsc⟩
    exact ⟨s,hsr.trans hrq,τ,s,(S.edge_mix f a H hH hf ha τ s).mpr ⟨j,hj,ht⟩,le_rfl,heq⟩

/-- Any coherent family is equal to its mixture below its activation
condition. This applies in particular to antichains, when coherence is vacuous. -/
theorem eq_mix_at (f : ι → S.Name) (a : ι → P) (H : Subgroup Γ) (hH : H ∈ S.filter)
    (hf : ∀ g ∈ H, ∀ i, g • f i = f i)
    (ha : ∀ g ∈ H, ∀ i, S.move g (a i) = a i)
    (hcoh : ∀ i j p, p ≤ a i → p ≤ a j → S.atomic.EqF p (f i) (f j)) (i : ι) :
    S.atomic.EqF (a i) (S.mix f a H hH hf ha) (f i) := by
  apply S.eq_of_same_members
  intro ν q hqi
  constructor
  · intro h
    apply S.atomic_regular.2 q ν (f i)
    intro r hrq
    obtain ⟨s,hsr,j,hsj,hm⟩ := (S.mem_mix f a H hH hf ha ν q).mp h r hrq
    exact ⟨s,hsr,(S.atomic.mem_congr (S.atomic.eq_refl s ν)
      (hcoh j i s hsj (hsr.trans (hrq.trans hqi)))).mp hm⟩
  · intro h
    apply (S.mem_mix f a H hH hf ha ν q).mpr
    intro r hrq
    exact ⟨r,le_rfl,i,hrq.trans hqi,S.atomic.mem_mono hrq h⟩

end
end PartitionConsistency.SetForcingNames.SymmetricSystem


/-! ## EquivariantMix -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w t
noncomputable section
variable {P : Type w} [Preorder P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)
variable {ι : Type t} [Small.{u} ι]

omit [Small.{u} ι] in
/-- An equivariant family need not have each member fixed pointwise.
Permuting the names together with their activation conditions suffices. -/
theorem equivariantMixTest_permute (f : ι → S.Name) (a : ι → P) (H : Subgroup Γ)
    (hperm : ∀ g ∈ H, ∀ i, ∃ j, f j = g • f i ∧ a j = S.move g (a i)) :
    ∀ g ∈ H, ∀ (i : S.MixEntries f) p, S.mixTest f a i p →
      ∃ j : S.MixEntries f, (f j.1).child j.2.property = g • (f i.1).child i.2.property ∧
        S.mixTest f a j (S.move g p) := by
  intro g hg i p hp
  obtain ⟨j,hfj,haj⟩ := hperm g hg i.1
  have he := S.entry_permute g (f i.1) i.2
  rw [← hfj] at he
  obtain ⟨k,hk⟩ := he
  refine ⟨⟨j,k⟩,hk,?_,?_⟩
  · change S.move g p ≤ a j
    rw [haj]
    exact (S.move g).monotone hp.1
  · change S.atomic.MemF (S.move g p) ((f j).child k.property) (f j)
    rw [hk,hfj]
    exact (S.mem_symmetry g p _ (f i.1)).mp hp.2

/-- Union of an equivariant family of active arbitrary-rank names.
No choice of a common strengthening occurs in the definition. -/
def equivariantMix (f : ι → S.Name) (a : ι → P) (H : Subgroup Γ) (hH : H ∈ S.filter)
    (hperm : ∀ g ∈ H, ∀ i, ∃ j, f j = g • f i ∧ a j = S.move g (a i)) : S.Name :=
  S.collect (fun i : S.MixEntries f => (f i.1).child i.2.property)
    (S.mixTest f a) H hH (S.equivariantMixTest_permute f a H hperm)

theorem equivariantMix_fixed (f : ι → S.Name) (a : ι → P) (H : Subgroup Γ) (hH : H ∈ S.filter)
    (hperm : ∀ g ∈ H, ∀ i, ∃ j, f j = g • f i ∧ a j = S.move g (a i)) (g : Γ) (hg : g ∈ H) :
    g • S.equivariantMix f a H hH hperm = S.equivariantMix f a H hH hperm :=
  Subtype.ext (S.collectName_fixed _ _ H (S.equivariantMixTest_permute f a H hperm) g hg)

theorem edge_equivariantMix (f : ι → S.Name) (a : ι → P) (H : Subgroup Γ) (hH : H ∈ S.filter)
    (hperm : ∀ g ∈ H, ∀ i, ∃ j, f j = g • f i ∧ a j = S.move g (a i)) (ν : S.Name) (p : P) :
    ZFSet.pair ν.raw (S.code p) ∈ (S.equivariantMix f a H hH hperm).raw ↔
      ∃ i : S.MixEntries f, (f i.1).child i.2.property = ν ∧ S.mixTest f a i p := by
  change ZFSet.pair ν.raw (S.code p) ∈
    S.collectRaw (fun i : S.MixEntries f => (f i.1).child i.2.property) (S.mixTest f a) ↔ _
  rw [S.edge_collectRaw]
  constructor
  · rintro ⟨i,c,hi,hν,hc⟩
    obtain rfl := S.code_injective hc
    exact ⟨i,Name.ext hν,hi⟩
  · rintro ⟨i,hi,hR⟩
    exact ⟨i,p,hR,congrArg Name.raw hi,rfl⟩

/-- The exact regular forcing value of membership in the union mixture. -/
theorem mem_equivariantMix (f : ι → S.Name) (a : ι → P) (H : Subgroup Γ) (hH : H ∈ S.filter)
    (hperm : ∀ g ∈ H, ∀ i, ∃ j, f j = g • f i ∧ a j = S.move g (a i)) (ν : S.Name) (p : P) :
    S.atomic.MemF p ν (S.equivariantMix f a H hH hperm) ↔
      ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ i : ι, r ≤ a i ∧ S.atomic.MemF r ν (f i) := by
  constructor
  · intro h q hqp
    obtain ⟨r,hrq,τ,c,he,hrc,heq⟩ := S.mem_iff.mp h q hqp
    obtain ⟨i,hi,hia,hit⟩ := (S.edge_equivariantMix f a H hH hperm τ c).mp he
    change S.atomic.MemF c ((f i.1).child i.2.property) (f i.1) at hit
    rw [hi] at hit
    exact ⟨r,hrq,i.1,hrc.trans hia,
      (S.atomic.mem_congr heq (S.atomic.eq_refl r (f i.1))).mpr (S.atomic.mem_mono hrc hit)⟩
  · intro h
    apply S.mem_iff.mpr
    intro q hqp
    obtain ⟨r,hrq,i,hria,hν⟩ := h q hqp
    obtain ⟨s,hsr,τ,c,he,hsc,heq⟩ := S.mem_iff.mp hν r le_rfl
    let j : S.MixEntries f := ⟨i,⟨(τ.raw,S.code c),he⟩⟩
    have hj : (f j.1).child j.2.property = τ := Name.ext rfl
    have ht : S.mixTest f a j s := by
      change s ≤ a i ∧ S.atomic.MemF s ((f i).child he) (f i)
      exact ⟨hsr.trans hria,S.mem_of_edge he hsc⟩
    exact ⟨s,hsr.trans hrq,τ,s,(S.edge_equivariantMix f a H hH hperm τ s).mpr ⟨j,hj,ht⟩,le_rfl,heq⟩

/-- Any coherent family is equal to its mixture below its activation
condition. This applies in particular to antichains, when coherence is vacuous. -/
theorem eq_equivariantMix_at (f : ι → S.Name) (a : ι → P) (H : Subgroup Γ) (hH : H ∈ S.filter)
    (hperm : ∀ g ∈ H, ∀ i, ∃ j, f j = g • f i ∧ a j = S.move g (a i))
    (hcoh : ∀ i j p, p ≤ a i → p ≤ a j → S.atomic.EqF p (f i) (f j)) (i : ι) :
    S.atomic.EqF (a i) (S.equivariantMix f a H hH hperm) (f i) := by
  apply S.eq_of_same_members
  intro ν q hqi
  constructor
  · intro h
    apply S.atomic_regular.2 q ν (f i)
    intro r hrq
    obtain ⟨s,hsr,j,hsj,hm⟩ := (S.mem_equivariantMix f a H hH hperm ν q).mp h r hrq
    exact ⟨s,hsr,(S.atomic.mem_congr (S.atomic.eq_refl s ν)
      (hcoh j i s hsj (hsr.trans (hrq.trans hqi)))).mp hm⟩
  · intro h
    apply (S.mem_equivariantMix f a H hH hperm ν q).mpr
    intro r hrq
    exact ⟨r,le_rfl,i,hrq.trans hqi,S.atomic.mem_mono hrq h⟩

end
end PartitionConsistency.SetForcingNames.SymmetricSystem

end OAI
