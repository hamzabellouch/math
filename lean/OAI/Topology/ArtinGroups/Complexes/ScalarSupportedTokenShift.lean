import Mathlib
import OAI.Topology.ArtinGroups.Complexes.TokenShift
import OAI.Topology.ArtinGroups.Complexes.ScalarSupported

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I : Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma scalarSupported_tokenShift (E:BasedComplex Q (K:=K) I) (l c:ℤ) (x:I→K) :
    ScalarSupported Q (E.tokenShift Q) l c x ↔ ScalarSupported Q E (l-1) (c+1) x := by
  constructor <;> intro h i hi <;> apply h i <;> intro hh <;> apply hi
  · change (E.placement i).cochain-1+((E.placement i).internal+2)=l ∧
      (E.placement i).cochain-1=c at hh
    dsimp only [GeneratorPlacement.level]
    omega
  · change (E.placement i).cochain-1+((E.placement i).internal+2)=l ∧
      (E.placement i).cochain-1=c
    dsimp only [GeneratorPlacement.level] at hh
    omega

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma scalarDifferential_tokenShift (E:BasedComplex Q (K:=K) I) (α:V) :
    (E.tokenShift Q).differential.map (vertexHom Q α)=
      -E.differential.map (vertexHom Q α) := by
  apply Matrix.ext
  intro i j
  exact map_neg (vertexHom Q α) _

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
theorem scalarExact_tokenShift_iff (E:BasedComplex Q (K:=K) I) (α:V) (l c:ℤ) :
    ScalarExactAt Q (E.tokenShift Q) α l c ↔ ScalarExactAt Q E α (l-1) (c+1) := by
  constructor
  · intro h x hx hd
    have hxs:ScalarSupported Q (E.tokenShift Q) l c x :=
      (scalarSupported_tokenShift Q E l c x).mpr hx
    have hdx:Matrix.vecMul x ((E.tokenShift Q).differential.map (vertexHom Q α))=0 := by
      rw [scalarDifferential_tokenShift,Matrix.vecMul_neg,hd,neg_zero]
    obtain ⟨y,hy,hyb⟩:=h x hxs hdx
    refine ⟨-y,?_,?_⟩
    · have hh:ScalarSupported Q E (l-1-1) (c-1+1) y :=
        (scalarSupported_tokenShift Q E (l-1) (c-1) y).mp hy
      intro i hi
      change -y i=0
      rw [hh i,neg_zero]
      simpa only [sub_add_cancel,add_sub_cancel_right] using hi
    · rw [scalarDifferential_tokenShift,Matrix.vecMul_neg] at hyb
      simpa only [Matrix.neg_vecMul] using hyb
  · intro h x hx hd
    have hxs:ScalarSupported Q E (l-1) (c+1) x :=
      (scalarSupported_tokenShift Q E l c x).mp hx
    have hdx:Matrix.vecMul x (E.differential.map (vertexHom Q α))=0 := by
      rw [scalarDifferential_tokenShift,Matrix.vecMul_neg] at hd
      exact neg_eq_zero.mp hd
    obtain ⟨y,hy,hyb⟩:=h x hxs hdx
    refine ⟨-y,?_,?_⟩
    · apply (scalarSupported_tokenShift Q E (l-1) (c-1) (-y)).mpr
      intro i hi
      change -y i=0
      rw [hy i,neg_zero]
      simpa only [sub_add_cancel,add_sub_cancel_right] using hi
    · rw [scalarDifferential_tokenShift,Matrix.vecMul_neg,Matrix.neg_vecMul,neg_neg,hyb]

theorem positiveTwist_test_exact_iff (hn:∀ a,Q.source a≠Q.target a)
    (E:BasedComplex Q (K:=K) I) (α:V) (l c:ℤ) :
    ScalarExactAt Q ((E.positiveTwist Q α).testComplex Q α) α l c ↔
      ScalarExactAt Q (E.testComplex Q α) α (l-1) (c+1) := by
  have e:=positiveTwist_testShift Q hn E α
  rw [← scalarExact_tokenShift_iff Q (E.testComplex Q α) α l c]
  constructor
  · exact fun h=>scalarExact_transport Q _ _ (e.symm Q) α (fun _=>rfl) h
  · exact fun h=>scalarExact_transport Q _ _ e α (fun _=>rfl) h

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
