import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.SphericalLongest

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} (M:CoxeterMatrix S)

noncomputable def topBlockMatchingKey (s:S) (T:Finset S) : ℕ :=
  2*(T.erase s).card+if s∈T then 0 else 1

def TopBlockStep (s:S) (A B:Finset S) : Prop :=
  (s∉A ∧ B=insert s A) ∨ ∃t:S,t≠s ∧ t∉B ∧ A=insert t B

lemma topBlockStep_key {s:S} {A B:Finset S} (h:TopBlockStep s A B) :
    topBlockMatchingKey s B<topBlockMatchingKey s A := by
  rcases h with ⟨hs,rfl⟩|⟨t,ht,htB,rfl⟩
  · simp [topBlockMatchingKey,hs]
  · have hte:t∉B.erase s:=fun h=>htB (Finset.mem_of_mem_erase h)
    have he:(insert t B).erase s=insert t (B.erase s):=Finset.erase_insert_of_ne ht
    rw [topBlockMatchingKey,topBlockMatchingKey,he,Finset.card_insert_of_notMem hte]
    have hs:s∈insert t B ↔ s∈B:=by simp [Ne.symm ht]
    simp only [hs]
    omega

theorem topBlockStep_wellFounded (s:S) :
    WellFounded (fun B A:Finset S=>TopBlockStep s A B) :=
  (measure (topBlockMatchingKey s)).wf.mono (fun _ _ h=>topBlockStep_key h)

lemma spherical_type_mono {R T:Set S} (h:R⊆T) (hT:IsSpherical M T) : IsSpherical M R := by
  let : Finite (coxeterParabolic M T):=hT
  exact Finite.of_injective
    (fun z:coxeterParabolic M R=>(⟨z,coxeterParabolic_mono M h z.property⟩:coxeterParabolic M T))
    (fun a b he=>Subtype.ext (congrArg (fun z:coxeterParabolic M T=>(z:M.Group)) he))

section FirstDescent
variable [Fintype S] [LinearOrder S] (z:M.Group)
  (hz:∀w,M.toCoxeterSystem.length w≤M.toCoxeterSystem.length z)
  (b:PositiveArtin M) (hb:b≠1)

noncomputable def firstPositiveDescent : S :=
  (PositiveDescentSet M b).toFinset.min'
    (Set.toFinset_nonempty.mpr (positiveDescentSet_nonempty M z hz hb))

lemma firstPositiveDescent_mem : firstPositiveDescent M z hz b hb∈PositiveDescentSet M b := by
  exact Set.mem_toFinset.mp (Finset.min'_mem _ _)

lemma firstPositiveDescent_le {s:S} (hs:s∈PositiveDescentSet M b) :
    firstPositiveDescent M z hz b hb ≤ s :=
  Finset.min'_le _ _ (Set.mem_toFinset.mpr hs)

theorem firstPositiveDescent_matched_face
    (cancel:∀a d e:PositiveArtin M,a*d=a*e→d=e)
    (R:Set S) (hR:R⊆PositiveDescentSet M b)
    (hn:firstPositiveDescent M z hz b hb∉R) :
    ∃hRs:IsSpherical M R,∃hTs:IsSpherical M (insert (firstPositiveDescent M z hz b hb) R),
      cellWithTop M (positiveToArtin M b) ⟨R,hRs⟩ <
      cellWithTop M (positiveToArtin M b) ⟨insert (firstPositiveDescent M z hz b hb) R,hTs⟩ := by
  have hD:=(positive_descent_fundamental M z hz cancel b).1
  have hRs:=spherical_type_mono M hR hD
  have hTs:=spherical_type_mono M (Set.insert_subset (firstPositiveDescent_mem M z hz b hb) hR) hD
  refine ⟨hRs,hTs,lt_of_le_of_ne (cellWithTop_mono M _ (Set.subset_insert _ _)) ?_⟩
  intro he
  have hset:R=insert (firstPositiveDescent M z hz b hb) R:=
    congrArg (fun a:LiftedCell M=>a.2.val) he
  apply hn
  rw [hset]
  exact Set.mem_insert _ _

end FirstDescent
end HarmonicArtin

end OAI
