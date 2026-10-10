import OAI.Topology.ArtinGroups.ParabolicIntersections.MeshQuiverWords

namespace OAI

/-! Finite positive Cartan quivers satisfy the explicit mesh ideal bound. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A R : Type} [Fintype V] [Fintype A]
  (Q : ReversibleQuiver V A) (U : Set V)
  (hloop : ∀ a, Q.source a≠Q.target a) (hsimple : QuiverSimpleOn Q U)
  [Ring R] [Algebra ℂ R]
noncomputable local instance (priority := 2000) meshRegionDecEq : DecidableEq U := Classical.decEq U
include hsimple

omit [Algebra ℂ R] in
lemma meshArrowValues_relation (B : A → R)
    (houtside : ∀ a, Q.source a∉U ∨ Q.target a∉U → B a=0)
    (hmesh : ∀ v∈U, (∑ a, if Q.source a=v then B a*B (Q.reverse a) else 0)=0)
    (v : U) :
    (∑ u : {u : U // (meshQuiverGraph Q U hloop).Adj u v},
      meshArrowValues Q U hloop B v u.val u.property.symm *
        meshArrowValues Q U hloop B u.val v u.property)=0 := by
  let p : A → Prop := fun a => Q.source a=v.val ∧ Q.target a∈U
  let f : A → R := fun a => if Q.source a=v.val then B a*B (Q.reverse a) else 0
  have hrest : (∑ a : {a : A // ¬p a}, f a)=0 := by
    apply Finset.sum_eq_zero
    intro a _
    by_cases hs : Q.source a=v.val
    · have ht : Q.target a∉U := fun ht => a.property ⟨hs,ht⟩
      simp only [f,hs,ite_true,houtside a (Or.inr ht),zero_mul]
    · simp only [f,hs,ite_false]
  have hsum := Fintype.sum_subtype_add_sum_subtype p f
  rw [hrest,add_zero] at hsum
  calc
    _ = ∑ a : {a : A // p a}, B a*B (Q.reverse a) := by
      apply Fintype.sum_equiv (meshQuiverNeighborEquiv Q U hloop hsimple v)
      intro u
      change B (meshChosenArrow Q U hloop u.property.symm) *
        B (meshChosenArrow Q U hloop u.property)=
        B (meshChosenArrow Q U hloop u.property.symm) *
          B (Q.reverse (meshChosenArrow Q U hloop u.property.symm))
      rw [←meshChosenArrow_reverse Q U hloop hsimple u.property.symm]
    _ = ∑ a : {a : A // p a}, f a := by
      apply Finset.sum_congr rfl
      intro a _
      exact (ite_eq_left a.property.1).symm
    _ = ∑ a, f a := hsum
    _ = 0 := hmesh v.val v.property

theorem quiver_mesh_words_vanish
    (hcartan : ((2 : ℝ) • (1 : Matrix U U ℝ)-(meshQuiverGraph Q U hloop).adjMatrix ℝ).PosDef)
    (B : A → R)
    (houtside : ∀ a, Q.source a∉U ∨ Q.target a∉U → B a=0)
    (hpath : ∀ a b, Q.target a≠Q.source b → B a*B b=0)
    (hmesh : ∀ v∈U, (∑ a, if Q.source a=v then B a*B (Q.reverse a) else 0)=0) :
    ∃ N : ℕ, 0<N ∧ ∀ w : List A, w.length=N → (w.map B).prod=0 := by
  obtain ⟨N,hN,hzero⟩ := positive_cartan_mesh_paths_vanish (meshQuiverGraph Q U hloop)
    hcartan (meshArrowValues Q U hloop B) (meshArrowValues_relation Q U hloop hsimple B houtside hmesh)
  refine ⟨N,hN,?_⟩
  intro w hw
  rcases mesh_word_is_path Q U hloop hsimple B houtside hpath w with hz|hwnil|⟨v,p,hp,_⟩
  · exact hz
  · subst w
    simp only [List.length_nil] at hw
    omega
  · subst N
    exact hp.symm.trans (hzero v p)

/-- The exact free-algebra ideal statement used in the conditional main
theorems, now proved for every finite simple positive Cartan quiver. -/
theorem meshNilpotent_of_positive_cartan
    (hcartan : ((2 : ℝ) • (1 : Matrix U U ℝ)-(meshQuiverGraph Q U hloop).adjMatrix ℝ).PosDef) :
    MeshNilpotent Q U := by
  let I : TwoSidedIdeal (FreeAlgebra ℂ A) := TwoSidedIdeal.span (meshRelations Q U)
  let φ : FreeAlgebra ℂ A →ₐ[ℂ] I.ringCon.Quotient := I.ringCon.mkₐ ℂ
  let B : A → I.ringCon.Quotient := fun a => φ (FreeAlgebra.ι ℂ a)
  have hmem (z : FreeAlgebra ℂ A) : z∈I ↔ φ z=0 := by
    have hk : z∈TwoSidedIdeal.ker I.ringCon.mk' ↔ z∈I := by
      rw [TwoSidedIdeal.ker_ringCon_mk']
    exact hk.symm.trans (TwoSidedIdeal.mem_ker I.ringCon.mk')
  have houtside : ∀ a, Q.source a∉U ∨ Q.target a∉U → B a=0 := by
    intro a ha
    apply (hmem _).mp
    exact TwoSidedIdeal.subset_span (Or.inl (Or.inl ⟨a,ha,rfl⟩))
  have hpath : ∀ a b, Q.target a≠Q.source b → B a*B b=0 := by
    intro a b hab
    change φ (FreeAlgebra.ι ℂ a)*φ (FreeAlgebra.ι ℂ b)=0
    rw [←map_mul]
    apply (hmem _).mp
    exact TwoSidedIdeal.subset_span (Or.inl (Or.inr ⟨a,b,hab,rfl⟩))
  have hmesh : ∀ v∈U, (∑ a, if Q.source a=v then B a*B (Q.reverse a) else 0)=0 := by
    intro v hv
    have hz : φ (meshRelation Q v)=0 := (hmem _).mp
      (TwoSidedIdeal.subset_span (Or.inr ⟨v,hv,rfl⟩))
    simpa only [meshRelation,map_sum,apply_ite,map_mul,map_zero] using hz
  obtain ⟨N,hN,hwords⟩ := quiver_mesh_words_vanish Q U hloop hsimple hcartan B houtside hpath hmesh
  refine ⟨N,hN,?_⟩
  intro w hw
  apply (hmem _).mpr
  simpa only [B,map_list_prod,List.map_map,Function.comp_def] using hwords w hw

end HarmonicArtin.ParabolicIntersections

end OAI
