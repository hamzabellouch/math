import OAI.RepresentationTheory.Saxl.StripReduction

namespace OAI

noncomputable section

open scoped TensorProduct

universe uV

namespace Saxl

lemma SizedStripChain.of_horizontal {ν μ : YoungDiagram} (hs : HorizontalStrip ν μ) :
    SizedStripChain [μ.card-ν.card] ν μ := by
  have hc : ν.card ≤ μ.card := Finset.card_le_card hs.1
  exact SizedStripChain.snoc (SizedStripChain.nil ν) hs (Nat.add_sub_of_le hc)

lemma StripChain.sized {q ν μ} (hs : StripChain q ν μ) :
    ∃ bs : List ℕ, bs.length = q ∧ SizedStripChain bs ν μ := by
  induction hs with
  | nil μ => exact ⟨[],rfl,SizedStripChain.nil μ⟩
  | @snoc q ν η μ hs hh hn ih =>
    obtain ⟨bs,hbs,hS⟩ := ih
    have hc : η.card ≤ μ.card := Finset.card_le_card hh.1
    exact ⟨bs++[μ.card-η.card], by simp [hbs], SizedStripChain.snoc hS hh (Nat.add_sub_of_le hc)⟩

/- Lift the factor support through the exact same-high quotient. -/
theorem band_cut_support (h s m : ℕ) (he : h+s=m)
    (ν μ : YoungDiagram) (hν : ν.card = (staircase h).card)
    (t : Tableau (staircase m).card μ) (bs : List ℕ) (hs : SizedStripChain bs ν μ)
    (fh : Representation.IntertwiningMap (spechtRep (canonicalTableau ν hν))
      (staircaseCyclic h).toRepresentation) (hfh : fh ≠ 0)
    (hband : ∀ (η : YoungDiagram) (r : Tableau (bandSize h s) η), η.colLen 0 ≤ bs.length →
      ∃ F : Representation.IntertwiningMap (spechtRep r)
        (cyclic (wordRep _ _) (stairBandWord h s)).toRepresentation, F ≠ 0) :
    ∃ F : Representation.IntertwiningMap (spechtRep t) (staircaseCyclic m).toRepresentation, F ≠ 0 := by
  subst m
  obtain ⟨f,hf⟩ := shiftedStairWord_support h s ν (canonicalTableau ν hν) fh hfh
  have H := strip_product_support hs (canonicalTableau ν hν) t (cutPositions h s)
    (shiftedStairWord h s) (stairBandWord h s)
    (fun a => s ≤ ((finProdFinEquiv.symm a).1).val)
    (shiftedStairWord_alphabet h s) (stairBandWord_alphabet h s) f hf hband
  rw [← staircase_cut_factor] at H
  obtain ⟨F,hF⟩ := H
  exact cyclic_projection_support (sameHighProjection _ _ _ s) (staircaseWord (h+s)) F hF

lemma staircase_one_dominates (μ : YoungDiagram) (hμ : μ.card = (staircase 1).card) :
    Dominates (staircase 1) μ := by
  intro k
  by_cases hk : k=0
  · subst k; simp [rowPrefix]
  · have hh : (staircase 1).colLen 0 ≤ k := by simp only [staircase_colLen]; omega
    rw [rowPrefix_eq_card _ hh,← hμ]
    exact rowPrefix_le_card μ k

/- Strong induction, including m=1 and every
partition of the exact triangular size. -/
theorem full_cyclic_support (m : ℕ) (hm : 1 ≤ m) (μ : YoungDiagram)
    (t : Tableau (staircase m).card μ) :
    ∃ F : Representation.IntertwiningMap (spechtRep t) (staircaseCyclic m).toRepresentation, F ≠ 0 := by
  induction m using Nat.strong_induction_on generalizing μ with
  | h m ih =>
    have hμ : μ.card = (staircase m).card := by
      simpa only [Fintype.card_fin,Fintype.card_coe] using (Fintype.card_congr t).symm
    by_cases hd : Dominates (staircase m) μ
    · exact dominated_support m hm μ t hd
    have hm2 : 2 ≤ m := by
      by_contra hn
      have he : m=1 := by omega
      subst m
      exact hd (staircase_one_dominates μ hμ)
    rcases strip_reduction m hm2 μ hμ hd with ⟨ν,hν,hs⟩ | ⟨hm5,q,hq,ν,hν,hs⟩
    · obtain ⟨f,hf⟩ := ih (m-1) (by omega) (by omega) ν (canonicalTableau ν hν)
      exact band_cut_support (m-1) 1 m (by omega) ν μ hν t [μ.card-ν.card]
        (SizedStripChain.of_horizontal hs) f hf (fun η r hη => oneBand_support (m-1) η r hη)
    · obtain ⟨f,hf⟩ := ih (m-2) (by omega) (by omega) ν (canonicalTableau ν hν)
      obtain ⟨bs,hbs,hS⟩ := hs.sized
      exact band_cut_support (m-2) 2 m (by omega) ν μ hν t bs hS f hf
        (fun η r hη => twoBand_support (m-2) (by omega) η r (by omega))

/- The strengthened cyclic form of Saxl’s conjecture. -/
theorem cyclic_saxl_conjecture : CyclicSaxlConjecture := by
  intro m hm μ hμ
  exact full_cyclic_support m hm μ (canonicalTableau μ hμ)

/- Every complex staircase tensor square contains
all Specht irreducibles of its symmetric group. -/
theorem saxl_conjecture : SaxlConjecture := saxl_of_cyclic_support cyclic_saxl_conjecture



theorem cyclic_saxl : CyclicSaxlConjecture := cyclic_saxl_conjecture

/- Specht classification implies that every finite-dimensional irreducible
complex representation embeds in the staircase tensor square. -/
theorem saxl_contains_every_irreducible (m : ℕ) (hm : 1 ≤ m)
    {V : Type uV} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Fin (staircase m).card)) V)
    [Representation.IsIrreducible ρ] :
    ∃ F : Representation.IntertwiningMap ρ
      ((spechtRep (stairTableau m)).tprod (spechtRep (stairTableau m))),
      Function.Injective F := by
  obtain ⟨p,⟨e⟩⟩ := irreducible_equiv_specht ρ
  obtain ⟨f,hf⟩ := full_cyclic_support m hm (partitionDiagram p) (partitionTableau p)
  let := specht_irreducible (partitionTableau p)
  have hi := (Representation.IsIrreducible.injective_or_eq_zero f).resolve_right hf
  exact ⟨((staircaseToTensor m).comp f).comp e.toIntertwiningMap,
    (staircaseToTensor_injective m).comp (hi.comp e.injective)⟩

/- The positive-multiplicity conclusion with the literal
triangular degree, rather than the definitionally convenient cell count. -/
theorem saxl_kronecker_pos (m : ℕ) (hm : 1 ≤ m) (μ : YoungDiagram)
    (hμ : μ.card = m * (m + 1) / 2) :
    0 < kronecker (canonicalTableau (staircase m) (staircase_card m))
      (canonicalTableau (staircase m) (staircase_card m)) (canonicalTableau μ hμ) := by
  have H : ∀ (n : ℕ) (hn : (staircase m).card = n) (hnu : μ.card = n),
      0 < kronecker (canonicalTableau (staircase m) hn)
        (canonicalTableau (staircase m) hn) (canonicalTableau μ hnu) := by
    intro n hn hnu
    subst n
    exact saxl_conjecture m hm μ hnu
  exact H _ (staircase_card m) hμ

end Saxl

end

end OAI
