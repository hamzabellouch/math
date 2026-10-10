import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.SphericalPair
import OAI.Topology.ArtinGroups.Harmonic.SphericalPacketWordProperty
import OAI.Topology.ArtinGroups.Coxeter.AlternatingLiftProd

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex CoxeterExchange

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] {K : Type*} [Field K]
  (M : CoxeterMatrix S)
local notation "Q" => fusionQuiver (fusionLabelSize M) (coxeterFusionEdge M) (coxeterFusionEdge_symm M)
local notation "P" => fusionWordPacketPerm (fusionLabelSize M) (coxeterFusionEdge M)
  (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M) (K:=K)
local notation "T" => fusionPacketPerm (fusionLabelSize M) (coxeterFusionEdge M)
  (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M) (K:=K)

theorem sourcePacket_braid (i j : S) :
    ((altList i j (M i j)).map fun s => T (Sum.inl s)).prod=
      ((altList j i (M i j)).map fun s => T (Sum.inl s)).prod := by
  by_cases hij : i=j
  · subst j; rfl
  by_cases hz : M i j=0
  · rw [hz]; rfl
  have hm : 2≤M i j := by have hh:=M.off_diagonal i j hij; omega
  let J : Set S := {i,j}
  let a : J := ⟨i,by simp [J]⟩
  let b : J := ⟨j,by simp [J]⟩
  have hab : a≠b := fun h => hij (congrArg Subtype.val h)
  have hJ : IsSpherical M J := spherical_pair M i j hm
  have hu := altList_reduced (restrictedMatrix M J).toCoxeterSystem a b hab (M i j)
    (Or.inr (le_refl (M i j)))
  have hv := altList_reduced (restrictedMatrix M J).toCoxeterSystem b a hab.symm (M i j)
    (Or.inr (le_of_eq (M.symmetric i j)))
  have he := altList_braid (restrictedMatrix M J).toCoxeterSystem a b
  have hh := spherical_packet_word_property M (K:=K) J hJ
    (altList a b (M i j)) (altList b a (M i j)) hu hv he
  rw [fusionWordPacketPerm_positive,fusionWordPacketPerm_positive] at hh
  simp only [altList_map,a,b] at hh
  simpa only [← altList_map,List.map_map,Function.comp_def] using hh

lemma sourcePacket_relators : ∀ r∈braidRelators M,
    FreeGroup.lift (fun s => T (Sum.inl s)) r=1 := by
  rintro r ⟨⟨i,j⟩,rfl⟩
  rw [map_mul,map_inv]
  apply mul_inv_eq_one.mpr
  rw [alternating_lift_prod,alternating_lift_prod]
  exact sourcePacket_braid M (K:=K) i j

noncomputable def sourceArtinAction :
    Artin M →* Equiv.Perm (FiniteHomotopyClass Q (K:=K)) :=
  PresentedGroup.toGroup (sourcePacket_relators M (K:=K))

lemma sourceArtinAction_generator (s : S) :
    sourceArtinAction M (K:=K) (generator M s)=T (Sum.inl s) :=
  PresentedGroup.toGroup.of _

end HarmonicArtin

end OAI
