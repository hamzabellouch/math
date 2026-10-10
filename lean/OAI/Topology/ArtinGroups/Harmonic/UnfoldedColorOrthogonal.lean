import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.UnfoldedHom
import OAI.Topology.ArtinGroups.Geometry.RootRowOrthogonalWord

namespace OAI

namespace HarmonicArtin
open Matrix Geometric CoxeterExchange
open scoped BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type*} [Fintype S] [LinearOrder S]

lemma unfolded_color_orthogonal (M : CoxeterMatrix S) (J : Set S) (hJ : IsSpherical M J)
    (α β : J × FusionLabel (fusionLabelSize M)) (hcolor : α.1=β.1) (hne : α≠β) :
    cartan (unfoldedMatrix M J) α β=0 := by
  rw [unfoldedMatrix_cartan M J hJ]
  simp [fusionUnfoldedCartan,hne,hcolor,coxeterFusionEdge_diag,
    FusionEdge.multiplicity]

theorem unfolded_reducedWord (M : CoxeterMatrix S) (J : Set S) (hJ : IsSpherical M J)
    (u : List J) (hu : (restrictedMatrix M J).toCoxeterSystem.IsReduced u) :
    (unfoldedMatrix M J).toCoxeterSystem.IsReduced (fusionExpandedWord (fusionLabelSize M) u) := by
  let c := (restrictedMatrix M J).toCoxeterSystem
  let d := (unfoldedMatrix M J).toCoxeterSystem
  obtain ⟨p,hp,hq⟩ := unfolded_strict_chamber M J hJ
  induction u with
  | nil => simp [fusionExpandedWord,CoxeterSystem.IsReduced]
  | cons i u ih =>
    have hru : c.IsReduced u := by simpa only [List.drop_succ_cons,List.drop_zero] using hu.drop 1
    have heu := ih hru
    let block := (Finset.univ : Finset (FusionLabel (fusionLabelSize M))).toList.map (fun L => (i,L))
    have hn : block.Nodup := List.Nodup.map (fun a b h => Prod.mk.inj h |>.2) (Finset.nodup_toList _)
    have hcolor : ∀ α∈block,α.1=i := by
      intro α hα
      obtain ⟨L,_,rfl⟩ := List.mem_map.mp hα
      rfl
    have horth : ∀ α∈block,∀ β∈block,α≠β → cartan (unfoldedMatrix M J) α β=0 := by
      intro α hα β hβ hne
      exact unfolded_color_orthogonal M J hJ α β ((hcolor α hα).trans (hcolor β hβ).symm) hne
    have ha : c.length (c.simple i*c.wordProd u)=c.length (c.wordProd u)+1 := by
      simpa only [CoxeterSystem.wordProd_cons,List.length_cons,← hru.eq] using hu.eq
    have has : ∀ α∈block,d.length (d.simple α*d.wordProd (fusionExpandedWord (fusionLabelSize M) u))=
        d.length (d.wordProd (fusionExpandedWord (fusionLabelSize M) u))+1 := by
      intro α hα
      apply (unfolded_left_ascent_iff M J hJ u α).mpr
      rw [hcolor α hα]
      exact ha
    have hb := orthogonal_ascent_block d (fusionFold (fusionLabelSize M) p) hq block hn horth
      (d.wordProd (fusionExpandedWord (fusionLabelSize M) u)) has
    change d.length (d.wordProd (block++fusionExpandedWord (fusionLabelSize M) u))=
      (block++fusionExpandedWord (fusionLabelSize M) u).length
    rw [d.wordProd_append,hb,List.length_append,heu.eq]

lemma fusionExpandedWord_length {E V : Type*} [Fintype E] [DecidableEq E]
    (m : E → ℕ) (u : List V) :
    (fusionExpandedWord m u).length=u.length*Fintype.card (FusionLabel m) := by
  induction u with
  | nil => simp [fusionExpandedWord]
  | cons i u ih =>
    change (((Finset.univ : Finset (FusionLabel m)).toList.map (fun L => (i,L)))++
      fusionExpandedWord m u).length=_
    rw [List.length_append,List.length_map,Finset.length_toList,Finset.card_univ,ih,List.length_cons]
    ring

theorem unfoldedHom_length (M : CoxeterMatrix S) (J : Set S) (hJ : IsSpherical M J)
    (w : (restrictedMatrix M J).Group) :
    (unfoldedMatrix M J).toCoxeterSystem.length (unfoldedHom M J hJ w)=
      (restrictedMatrix M J).toCoxeterSystem.length w*Fintype.card (FusionLabel (fusionLabelSize M)) := by
  obtain ⟨u,hu,he⟩ := (restrictedMatrix M J).toCoxeterSystem.exists_isReduced w
  rw [he,unfoldedHom_wordProd,(unfolded_reducedWord M J hJ u hu).eq,hu.eq,fusionExpandedWord_length]

end HarmonicArtin

end OAI
