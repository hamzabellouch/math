import OAI.Topology.ArtinGroups.ParabolicIntersections.AmalgamGraph
import Mathlib.Data.List.ChainOfFn

namespace OAI

/-! Reduced edge chains in the amalgamated product cannot close. -/
namespace HarmonicArtin.ParabolicIntersections.AmalgamTree
open Monoid
attribute [local instance] Classical.decEq Classical.propDecidable
variable {G : Bool → Type} [∀ b, Group (G b)] {H : Type} [Group H]
variable (φ : ∀ b, H →* G b)

/-- The normal-form theorem, expressed using a list of actual factor elements. -/
lemma reduced_word_not_base (hφ : ∀ b, Function.Injective (φ b))
    (w : List (Σ b, G b)) (hw : w≠[])
    (hchain : w.IsChain (fun a b => a.1≠b.1))
    (hred : ∀ a∈w, a.2∉(φ a.1).range) :
    (w.map (fun a => PushoutI.of (φ := φ) a.1 a.2)).prod∉(PushoutI.base φ).range := by
  intro h
  let W : CoprodI.Word G := ⟨w,by
    intro a ha he
    apply hred a ha
    exact ⟨1,(map_one _).trans he.symm⟩,hchain⟩
  have hr : PushoutI.Reduced φ W := hred
  have he : W=CoprodI.Word.empty := hr.eq_empty_of_mem_range hφ (by
    simpa only [CoprodI.Word.prod,map_list_prod,List.map_map,Function.comp_def,
      PushoutI.ofCoprodI_of] using h)
  exact hw (congrArg CoprodI.Word.toList he)

lemma transition_product (e : ℕ → Amalgam φ) (n : ℕ) :
    (List.ofFn (fun i : Fin n => (e i)⁻¹*e (i+1))).prod=(e 0)⁻¹*e n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ',List.prod_concat]
    change (List.ofFn (fun i : Fin n => (e i)⁻¹*e (i+1))).prod*((e n)⁻¹*e (n+1))=_
    rw [ih]
    group

/-- Consecutive edges with distinct edge cosets give a nontrivial reduced
word, provided their common vertex types alternate. -/
theorem transition_not_base (hφ : ∀ b, Function.Injective (φ b))
    (e : ℕ → Amalgam φ) (b : ℕ → Bool) (n : ℕ) (hn : 0<n)
    (hfactor : ∀ i<n, (e i)⁻¹*e (i+1)∈Factor φ (b i))
    (hdistinct : ∀ i<n, (e i)⁻¹*e (i+1)∉(PushoutI.base φ).range)
    (halt : ∀ i, i+1<n → b i≠b (i+1)) :
    (e 0)⁻¹*e n∉(PushoutI.base φ).range := by
  let a (i : Fin n) : G (b i) := Classical.choose (hfactor i i.isLt)
  have ha (i : Fin n) : PushoutI.of (φ := φ) (b i) (a i)=(e i)⁻¹*e (i+1) :=
    Classical.choose_spec (hfactor i i.isLt)
  let w : List (Σ b,G b) := List.ofFn (fun i : Fin n => ⟨b i,a i⟩)
  have hw : w≠[] := by
    intro h
    have := congrArg List.length h
    simp only [w,List.length_ofFn,List.length_nil] at this
    omega
  have hchain : w.IsChain (fun a b => a.1≠b.1) := by
    apply List.isChain_ofFn.mpr
    intro i hi
    exact halt i hi
  have hred : ∀ x∈w, x.2∉(φ x.1).range := by
    intro x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    rintro ⟨h,he⟩
    change φ (b i) h=a i at he
    apply hdistinct i i.isLt
    refine ⟨h,?_⟩
    rw [←ha i,←he]
    exact (PushoutI.of_apply_eq_base φ (b i) h).symm
  have hprod : (w.map (fun x => PushoutI.of (φ := φ) x.1 x.2)).prod=(e 0)⁻¹*e n := by
    dsimp only [w]
    rw [List.map_ofFn]
    change (List.ofFn (fun i : Fin n => PushoutI.of (φ := φ) (b i) (a i))).prod=_
    simp only [ha]
    exact transition_product φ e n
  rw [←hprod]
  exact reduced_word_not_base φ hφ w hw hchain hred

end HarmonicArtin.ParabolicIntersections.AmalgamTree

end OAI
