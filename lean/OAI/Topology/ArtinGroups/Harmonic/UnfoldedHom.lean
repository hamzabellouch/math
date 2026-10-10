import Mathlib
import OAI.Topology.ArtinGroups.Geometry.RootNonposDescent
import OAI.Topology.ArtinGroups.Harmonic.UnfoldedMatrix

namespace OAI

namespace HarmonicArtin
open Geometric CoxeterExchange
open scoped BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable

lemma fusionExpandedWord_append {E V : Type*} [Fintype E] [DecidableEq E] (m : E → ℕ)
    (u v : List V) : fusionExpandedWord m (u++v)=fusionExpandedWord m u++fusionExpandedWord m v := by
  simp only [fusionExpandedWord,List.flatMap_append]

lemma fusionExpandedWord_flatten_replicate {E V : Type*} [Fintype E] [DecidableEq E] (m : E → ℕ)
    (u : List V) (n : ℕ) : fusionExpandedWord m ((List.replicate n u).flatten)=
      (List.replicate n (fusionExpandedWord m u)).flatten := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ,List.flatten_cons,fusionExpandedWord_append,ih]

lemma wordProd_flatten_replicate {V W : Type*} [Group W] {N : CoxeterMatrix V}
    (cs : CoxeterSystem N W) (u : List V) (n : ℕ) :
    cs.wordProd ((List.replicate n u).flatten)=(cs.wordProd u)^n := by
  induction n with
  | zero => simp
  | succ n ih => simp only [List.replicate_succ,List.flatten_cons,cs.wordProd_append,ih,pow_succ']

variable {S : Type*} [Fintype S] [LinearOrder S]

noncomputable def unfoldedHom (M : CoxeterMatrix S) (J : Set S) (hJ : IsSpherical M J) :
    (restrictedMatrix M J).Group →* (unfoldedMatrix M J).Group :=
  (restrictedMatrix M J).toCoxeterSystem.lift
    ⟨fun i => (unfoldedMatrix M J).toCoxeterSystem.wordProd
      (fusionExpandedWord (fusionLabelSize M) [i]),by
      intro i j
      let c := (restrictedMatrix M J).toCoxeterSystem
      let d := (unfoldedMatrix M J).toCoxeterSystem
      have hword : c.wordProd ((List.replicate ((restrictedMatrix M J) i j) [i,j]).flatten)=1 := by
        rw [wordProd_flatten_replicate]
        simpa only [CoxeterSystem.wordProd_cons,CoxeterSystem.wordProd_nil,mul_one]
          using c.simple_mul_simple_pow i j
      have hu := unfolded_word_one M J hJ _ hword
      rw [fusionExpandedWord_flatten_replicate,wordProd_flatten_replicate] at hu
      have he : fusionExpandedWord (fusionLabelSize M) [i,j]=
          fusionExpandedWord (fusionLabelSize M) [i]++fusionExpandedWord (fusionLabelSize M) [j] :=
        fusionExpandedWord_append _ [i] [j]
      rw [he,d.wordProd_append] at hu
      exact hu⟩

@[simp] lemma unfoldedHom_simple (M : CoxeterMatrix S) (J : Set S) (hJ : IsSpherical M J) (i : J) :
    unfoldedHom M J hJ ((restrictedMatrix M J).toCoxeterSystem.simple i)=
      (unfoldedMatrix M J).toCoxeterSystem.wordProd (fusionExpandedWord (fusionLabelSize M) [i]) :=
  (restrictedMatrix M J).toCoxeterSystem.lift_apply_simple _ i

lemma unfoldedHom_wordProd (M : CoxeterMatrix S) (J : Set S) (hJ : IsSpherical M J) (u : List J) :
    unfoldedHom M J hJ ((restrictedMatrix M J).toCoxeterSystem.wordProd u)=
      (unfoldedMatrix M J).toCoxeterSystem.wordProd (fusionExpandedWord (fusionLabelSize M) u) := by
  induction u with
  | nil => simp [fusionExpandedWord]
  | cons i u ih =>
    rw [CoxeterSystem.wordProd_cons,map_mul,unfoldedHom_simple,ih]
    change _=(unfoldedMatrix M J).toCoxeterSystem.wordProd
      (fusionExpandedWord (fusionLabelSize M) ([i]++u))
    rw [fusionExpandedWord_append,CoxeterSystem.wordProd_append]

theorem unfolded_word_eq (M : CoxeterMatrix S) (J : Set S) (hJ : IsSpherical M J)
    (u v : List J) (h : (restrictedMatrix M J).toCoxeterSystem.wordProd u=
      (restrictedMatrix M J).toCoxeterSystem.wordProd v) :
    (unfoldedMatrix M J).toCoxeterSystem.wordProd (fusionExpandedWord (fusionLabelSize M) u)=
      (unfoldedMatrix M J).toCoxeterSystem.wordProd (fusionExpandedWord (fusionLabelSize M) v) := by
  rw [← unfoldedHom_wordProd M J hJ,← unfoldedHom_wordProd M J hJ,h]

theorem unfoldedHom_left_ascent (M : CoxeterMatrix S) (J : Set S) (hJ : IsSpherical M J)
    (w : (restrictedMatrix M J).Group) (α : J × FusionLabel (fusionLabelSize M)) :
    let c := (restrictedMatrix M J).toCoxeterSystem
    let d := (unfoldedMatrix M J).toCoxeterSystem
    d.length (d.simple α*unfoldedHom M J hJ w)=d.length (unfoldedHom M J hJ w)+1 ↔
      c.length (c.simple α.1*w)=c.length w+1 := by
  dsimp only
  obtain ⟨u,hu,he⟩ := (restrictedMatrix M J).toCoxeterSystem.exists_isReduced w
  rw [he,unfoldedHom_wordProd]
  exact unfolded_left_ascent_iff M J hJ u α

theorem unfoldedHom_right_ascent (M : CoxeterMatrix S) (J : Set S) (hJ : IsSpherical M J)
    (w : (restrictedMatrix M J).Group) (α : J × FusionLabel (fusionLabelSize M)) :
    let c := (restrictedMatrix M J).toCoxeterSystem
    let d := (unfoldedMatrix M J).toCoxeterSystem
    d.length (unfoldedHom M J hJ w*d.simple α)=d.length (unfoldedHom M J hJ w)+1 ↔
      c.length (w*c.simple α.1)=c.length w+1 := by
  dsimp only
  have h := unfoldedHom_left_ascent M J hJ w⁻¹ α
  dsimp only at h
  rw [map_inv,← inverse_right_length,← inverse_right_length,inv_inv,inv_inv,
    CoxeterSystem.length_inv,CoxeterSystem.length_inv] at h
  exact h

theorem unfoldedHom_right_descent (M : CoxeterMatrix S) (J : Set S) (hJ : IsSpherical M J)
    (w : (restrictedMatrix M J).Group) (α : J × FusionLabel (fusionLabelSize M)) :
    let c := (restrictedMatrix M J).toCoxeterSystem
    let d := (unfoldedMatrix M J).toCoxeterSystem
    d.length (unfoldedHom M J hJ w*d.simple α)+1=d.length (unfoldedHom M J hJ w) ↔
      c.length (w*c.simple α.1)+1=c.length w := by
  dsimp only
  have h := unfoldedHom_right_ascent M J hJ w α
  have h₁ := (unfoldedMatrix M J).toCoxeterSystem.length_mul_simple (unfoldedHom M J hJ w) α
  have h₂ := (restrictedMatrix M J).toCoxeterSystem.length_mul_simple w α.1
  dsimp only at h
  omega

theorem unfolded_finite (M : CoxeterMatrix S) (J : Set S) (hJ : IsSpherical M J) :
    Finite (unfoldedMatrix M J).Group := by
  let : Finite (restrictedMatrix M J).Group := restricted_finite M J hJ
  obtain ⟨z,hz⟩ := exists_longest (restrictedMatrix M J).toCoxeterSystem
  apply finite_of_all_descents (unfoldedMatrix M J).toCoxeterSystem (unfoldedHom M J hJ z)
  intro α
  exact (unfoldedHom_right_descent M J hJ z α).mpr
    (all_descents_of_longest (restrictedMatrix M J).toCoxeterSystem z hz α.1)

theorem unfolded_longest (M : CoxeterMatrix S) (J : Set S) (hJ : IsSpherical M J)
    (z : (restrictedMatrix M J).Group)
    (hz : ∀ w,(restrictedMatrix M J).toCoxeterSystem.length w≤
      (restrictedMatrix M J).toCoxeterSystem.length z) (v : (unfoldedMatrix M J).Group) :
    (unfoldedMatrix M J).toCoxeterSystem.length v≤
      (unfoldedMatrix M J).toCoxeterSystem.length (unfoldedHom M J hJ z) := by
  apply length_le_of_all_descents (unfoldedMatrix M J).toCoxeterSystem (unfoldedHom M J hJ z)
  intro α
  exact (unfoldedHom_right_descent M J hJ z α).mpr
    (all_descents_of_longest (restrictedMatrix M J).toCoxeterSystem z hz α.1)

end HarmonicArtin

end OAI
