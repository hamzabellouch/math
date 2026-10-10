import OAI.Topology.ArtinGroups.ParabolicIntersections.MeshQuiver

namespace OAI

/-! Nonzero arrow words are actual paths in the induced simple graph. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A R : Type} (Q : ReversibleQuiver V A) (U : Set V)
  (hloop : ∀ a, Q.source a≠Q.target a) (hsimple : QuiverSimpleOn Q U)
  [Ring R]

noncomputable def meshArrowValues (B : A → R) (u v : U)
    (h : (meshQuiverGraph Q U hloop).Adj u v) : R :=
  B (meshChosenArrow Q U hloop h)

include hsimple in
/-- The outside and noncomposable relations leave only genuine paths.
The last-vertex annihilation statement is maintained in the induction. -/
theorem mesh_word_is_path (B : A → R)
    (houtside : ∀ a, Q.source a∉U ∨ Q.target a∉U → B a=0)
    (hpath : ∀ a b, Q.target a≠Q.source b → B a*B b=0) (w : List A) :
    (w.map B).prod=0 ∨ w=[] ∨
      ∃ (v : U) (p : MeshPaths (meshQuiverGraph Q U hloop) w.length v),
        meshPathEvaluate (meshQuiverGraph Q U hloop) (meshArrowValues Q U hloop B)
          w.length v p=(w.map B).prod ∧
        ∀ a, Q.source a≠v.val → (w.map B).prod*B a=0 := by
  induction w using List.reverseRecOn with
  | nil => exact Or.inr (Or.inl rfl)
  | append_singleton w a ih =>
    by_cases hz : ((w++[a]).map B).prod=0
    · exact Or.inl hz
    have heq : ((w++[a]).map B).prod=(w.map B).prod*B a := by simp
    have hBa : B a≠0 := by
      intro ha
      apply hz
      rw [heq,ha,mul_zero]
    have hSa : Q.source a∈U := by
      by_contra h
      exact hBa (houtside a (Or.inl h))
    have hTa : Q.target a∈U := by
      by_contra h
      exact hBa (houtside a (Or.inr h))
    let target : U := ⟨Q.target a,hTa⟩
    have hkill : ∀ b, Q.source b≠target.val → ((w++[a]).map B).prod*B b=0 := by
      intro b hb
      rw [heq,mul_assoc,hpath a b hb.symm,mul_zero]
    right
    right
    rcases ih with hw | hw | ⟨v,p,hp,hv⟩
    · exact (hz (by rw [heq,hw,zero_mul])).elim
    · subst w
      let source : U := ⟨Q.source a,hSa⟩
      have edge : (meshQuiverGraph Q U hloop).Adj source target := ⟨a,rfl,rfl⟩
      refine ⟨target,⟨⟨source,edge⟩,PUnit.unit⟩,?_,hkill⟩
      simp only [List.nil_append,List.length_singleton,List.map_singleton,List.prod_singleton]
      change 1*B (meshChosenArrow Q U hloop edge)=B a
      rw [one_mul,meshChosenArrow_eq Q U hloop hsimple edge a rfl rfl]
    · have hsource : Q.source a=v.val := by
        by_contra h
        exact hz (heq.trans (hv a h))
      have edge : (meshQuiverGraph Q U hloop).Adj v target := ⟨a,hsource,rfl⟩
      rw [List.length_append,List.length_singleton]
      refine ⟨target,⟨⟨v,edge⟩,p⟩,?_,hkill⟩
      change meshPathEvaluate (meshQuiverGraph Q U hloop) (meshArrowValues Q U hloop B)
        w.length v p * B (meshChosenArrow Q U hloop edge)=_
      rw [hp,meshChosenArrow_eq Q U hloop hsimple edge a hsource rfl,heq]

end HarmonicArtin.ParabolicIntersections

end OAI
