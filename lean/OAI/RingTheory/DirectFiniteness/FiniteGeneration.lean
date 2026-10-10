import OAI.RingTheory.DirectFiniteness.ScalarFormulas

namespace OAI

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample

lemma coprod_fg {G H : Type} [Group G] [Group H] [Group.FG G] [Group.FG H] :
    Group.FG (Monoid.Coprod G H) := by
  obtain ⟨α, hα, f, hf⟩ := (Group.fg_iff_exists_freeGroup_hom_surjective_finite (G := G)).mp inferInstance
  obtain ⟨β, hβ, g, hg⟩ := (Group.fg_iff_exists_freeGroup_hom_surjective_finite (G := H)).mp inferInstance
  let j : FreeGroup (α ⊕ β) →* Monoid.Coprod G H :=
    FreeGroup.lift (Sum.elim (fun a => Monoid.Coprod.inl (f (FreeGroup.of a)))
      (fun b => Monoid.Coprod.inr (g (FreeGroup.of b))))
  have hl (a : FreeGroup α) : j (FreeGroup.map Sum.inl a) = Monoid.Coprod.inl (f a) := by
    have he : j.comp (FreeGroup.map Sum.inl) = Monoid.Coprod.inl.comp f := by
      apply FreeGroup.ext_hom
      intro x
      simp [j]
    exact DFunLike.congr_fun he a
  have hr (b : FreeGroup β) : j (FreeGroup.map Sum.inr b) = Monoid.Coprod.inr (g b) := by
    have he : j.comp (FreeGroup.map Sum.inr) = Monoid.Coprod.inr.comp g := by
      apply FreeGroup.ext_hom
      intro x
      simp [j]
    exact DFunLike.congr_fun he b
  apply Group.fg_of_surjective (f := j)
  intro x
  induction x using Monoid.Coprod.induction_on with
  | inl a =>
    obtain ⟨a', rfl⟩ := hf a
    exact ⟨FreeGroup.map Sum.inl a', hl a'⟩
  | inr b =>
    obtain ⟨b', rfl⟩ := hg b
    exact ⟨FreeGroup.map Sum.inr b', hr b'⟩
  | mul a b ha hb =>
    obtain ⟨a', rfl⟩ := ha
    obtain ⟨b', rfl⟩ := hb
    exact ⟨a' * b', map_mul j a' b'⟩

lemma multipleHNN_fg {H I : Type} [Group H] [Group.FG H] [Finite I]
    (A B : I → Subgroup H) (φ : ∀ i, A i ≃* B i) :
    Group.FG (MultipleHNN.Extension A B φ) := by
  have : Group.FG (Monoid.Coprod H (FreeGroup I)) := coprod_fg
  exact Group.fg_of_surjective (f := (MultipleHNN.con A B φ).mk') Con.mk'_surjective

end KaplanskyCounterexample
end

end OAI
