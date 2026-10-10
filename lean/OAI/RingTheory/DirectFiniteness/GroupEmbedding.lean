import OAI.RingTheory.DirectFiniteness.GluedWords

namespace OAI

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.GluedGroup
variable {V F : Type} (Inc : F → Finset V) (ℓ : ℕ)
variable (incMap : ∀ v : V, {f : F // v ∈ Inc f} → (ZMod ℓ →+ (Fin 2 → ZMod ℓ)))

lemma localEvaluation_word (v : V) (w : List (LocalGenerator Inc ℓ v × Bool)) :
    (localEvaluation Inc ℓ incMap v (FreeGroup.mk w)).toAdd =
      ((w.map (fun s => (s.1.val, s.2))).map (fun s =>
        totalMap Inc ℓ incMap v (signedToken ℓ s).1 (signedToken ℓ s).2)).sum := by
  rw [localEvaluation, FreeGroup.lift_mk, toAdd_list_sum,
    List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro s _
  rcases s with ⟨s, b⟩
  cases b <;> simp [signedToken, totalMap_of_mem, s.property]

lemma relators_allowed (g : FreeGroup (Generator (F := F) ℓ))
    (hg : g ∈ relators Inc ℓ incMap) :
    ∃ w, FreeGroup.mk w = g ∧ Allowed Inc ℓ incMap w := by
  obtain ⟨v, r, he, rfl⟩ := hg
  induction r using Quot.inductionOn with
  | h w =>
    refine ⟨w.map (fun s => (s.1.val, s.2)), rfl, v, ?_, ?_⟩
    · intro t ht
      simp only [List.map_map, List.mem_map] at ht
      obtain ⟨s, _, rfl⟩ := ht
      exact s.1.property
    · rw [List.map_map]
      have hh := congrArg Multiplicative.toAdd he
      change (localEvaluation Inc ℓ incMap v (FreeGroup.mk w)).toAdd = 0 at hh
      rw [localEvaluation_word] at hh
      exact hh

/-- No nonzero line generator collapses in the actual all-word presentation. -/
theorem generator_ne_one (hInc : ∀ f, (Inc f).Nonempty)
    (hinj : ∀ v f, v ∈ Inc f → Function.Injective (totalMap Inc ℓ incMap v f))
    (hind : ∀ v f g, v ∈ Inc f → v ∈ Inc g → f ≠ g →
      ∀ a b, totalMap Inc ℓ incMap v f a + totalMap Inc ℓ incMap v g b = 0 → a = 0)
    (hgirth : 12 ≤ (Planar.incidenceGraph (fun v f => v ∈ Inc f)).egirth)
    (g : Generator (F := F) ℓ) :
    PresentedGroup.of (rels := relators Inc ℓ incMap) g ≠ 1 := by
  intro he
  have h : WordReduction.Related (Allowed Inc ℓ incMap) [(g, true)] [] :=
    WordReduction.of_presented_eq_one (relators Inc ℓ incMap)
      (allowed_inv Inc ℓ incMap) (allowed_cancel Inc ℓ incMap hInc)
      (relators_allowed Inc ℓ incMap) [(g, true)] he
  have hi : Nonempty (Planar.OpenDiagram (fun v f => v ∈ Inc f)
      (totalMap Inc ℓ incMap) g.1 ([(g, true)].map (signedToken ℓ))) := by
    exact ⟨Planar.OpenDiagram.initial (fun v f => v ∈ Inc f) (totalMap Inc ℓ incMap)
      g.1 g.2.val g.2.property⟩
  have hf := (Planar.OpenDiagram.related_iff (Inc := fun v f => v ∈ Inc f)
    (ι := totalMap Inc ℓ incMap) (f₀ := g.1) (signedToken ℓ)
    (Allowed Inc ℓ incMap) (fun _ h => h) h).mp hi
  obtain ⟨D⟩ := hf
  obtain ⟨v, hv⟩ := hInc g.1
  exact D.not_empty g.1 v hv hinj hind hgirth

theorem theta_injective (hc : CoversPoints Inc ℓ incMap)
    (hInc : ∀ f, (Inc f).Nonempty)
    (hinj : ∀ v f, v ∈ Inc f → Function.Injective (totalMap Inc ℓ incMap v f))
    (hind : ∀ v f g, v ∈ Inc f → v ∈ Inc g → f ≠ g →
      ∀ a b, totalMap Inc ℓ incMap v f a + totalMap Inc ℓ incMap v g b = 0 → a = 0)
    (hgirth : 12 ≤ (Planar.incidenceGraph (fun v f => v ∈ Inc f)).egirth)
    (v : V) : Function.Injective (theta Inc ℓ incMap hc v) := by
  apply (theta Inc ℓ incMap hc v).ker_eq_bot_iff.mp
  apply bot_unique
  intro a ha
  change a = 1
  change theta Inc ℓ incMap hc v a = 1 at ha
  by_contra he
  have ha0 : a.toAdd ≠ 0 := by
    exact fun hh => he (by simpa only [ofAdd_toAdd, ofAdd_zero] using congrArg Multiplicative.ofAdd hh)
  obtain ⟨f, hf, c, hc0, hca⟩ := hc v a.toAdd ha0
  have ht := theta_generator Inc ℓ incMap hc v f hf c hc0
  have hv : Multiplicative.ofAdd (incMap v ⟨f, hf⟩ c) = a := congrArg Multiplicative.ofAdd hca
  rw [hv, ha] at ht
  exact generator_ne_one Inc ℓ incMap hInc hinj hind hgirth (f, ⟨c, hc0⟩) ht.symm

end KaplanskyCounterexample.GluedGroup
end

end OAI
