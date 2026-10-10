import OAI.Topology.ArtinGroups.ParabolicIntersections.AmalgamReduced

namespace OAI

/-! Reduced commutators in a two-factor amalgam. -/
namespace HarmonicArtin.ParabolicIntersections.AmalgamTree
attribute [local instance] Classical.decEq Classical.propDecidable
variable {G : Bool → Type} [∀ b, Group (G b)] {H : Type} [Group H]
variable (φ : ∀ b, H →* G b)

lemma factor_commutator_ne_one (hφ : ∀ b, Function.Injective (φ b))
    (a : G false) (b : G true) (ha : a∉(φ false).range) (hb : b∉(φ true).range) :
    Monoid.PushoutI.of (φ := φ) false a * Monoid.PushoutI.of true b *
      (Monoid.PushoutI.of false a)⁻¹ * (Monoid.PushoutI.of true b)⁻¹≠1 := by
  let w : List (Σ b,G b) := [⟨false,a⟩,⟨true,b⟩,⟨false,a⁻¹⟩,⟨true,b⁻¹⟩]
  have hn : w≠[] := by simp only [w,ne_eq,List.cons_ne_nil,not_false_eq_true]
  have hc : w.IsChain (fun a b => a.1≠b.1) := by
    simp [w,List.isChain_cons_cons]
  have hr : ∀ x∈w, x.2∉(φ x.1).range := by
    intro x hx
    simp only [w,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl
    · exact ha
    · exact hb
    · exact fun h => ha (by simpa only [inv_inv] using (φ false).range.inv_mem h)
    · exact fun h => hb (by simpa only [inv_inv] using (φ true).range.inv_mem h)
  have hh := reduced_word_not_base φ hφ w hn hc hr
  simp only [w,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,map_inv,mul_one] at hh
  intro he
  apply hh
  have he' : Monoid.PushoutI.of (φ := φ) false a *
      (Monoid.PushoutI.of true b * ((Monoid.PushoutI.of false a)⁻¹ *
        (Monoid.PushoutI.of true b)⁻¹))=1 := by simpa only [mul_assoc] using he
  rw [he']
  exact Subgroup.one_mem _

end HarmonicArtin.ParabolicIntersections.AmalgamTree

end OAI
