import OAI.Topology.ArtinGroups.ParabolicIntersections.AcyclicTwistInput
import OAI.Topology.ArtinGroups.Complexes.MinimalEmbedding
import OAI.Topology.ArtinGroups.Complexes.Cone

namespace OAI

/-! Discharging the acyclic-evaluation input by finite minimal reduction. -/
namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A : Type} (Q : ReversibleQuiver V A) [Fintype V] [Fintype A]
  [DecidableEq V] [DecidableEq A]

omit [Fintype V] [DecidableEq A] in
lemma minimal_scalar_exact_empty {I : Type} [Fintype I] [DecidableEq I]
    (E : BasedComplex Q (K := ℂ) I) (hE : E.IsMinimal Q) (α : V)
    (h : ∀ l c, ScalarExactAt Q E α l c) : IsEmpty I := by
  have hdm : E.differential.map (vertexHom Q α)=0 := by
    ext i j
    exact congrFun (hE i j) α
  refine ⟨fun i => ?_⟩
  let x : I → ℂ := Pi.single i 1
  have hx : ScalarSupported Q E (E.placement i).level (E.placement i).cochain x := by
    intro j hj
    have hji : j ≠ i := by rintro rfl; exact hj ⟨rfl,rfl⟩
    exact Pi.single_eq_of_ne hji _
  obtain ⟨y,_,hy⟩ := h _ _ x hx (by rw [hdm,Matrix.vecMul_zero])
  rw [hdm,Matrix.vecMul_zero] at hy
  have hi := congrFun hy i
  simp [x] at hi

omit [Fintype V] [DecidableEq A] in
/-- An everywhere exact, one-color complex has an empty minimal model. -/
lemma scalar_exact_empty_model {I : Type} [Fintype I] [DecidableEq I]
    (E : BasedComplex Q (K := ℂ) I) (α : V)
    (hcolor : ∀ i, (E.placement i).color=α)
    (h : ∀ l c, ScalarExactAt Q E α l c) :
    ∃ F : FiniteModel.{0} Q (K := ℂ), IsEmpty F.Index ∧
      Nonempty (HomotopyEquivalence Q F.complex E) := by
  obtain ⟨F,hF,⟨e⟩,j,hj⟩ := FiniteModel.exists_minimal_embedding Q (FiniteModel.ofComplex Q E)
  have hc : ∀ i, (F.complex.placement i).color=α := by
    intro i
    rw [hj i]
    exact hcolor (j i)
  have he : ∀ l c, ScalarExactAt Q F.complex α l c := fun l c =>
    scalarExact_transport Q F.complex E (e.symm Q) α hc (h l c)
  exact ⟨F,minimal_scalar_exact_empty Q F.complex hF α he,⟨e.symm Q⟩⟩

omit [Fintype V] [DecidableEq A] in
lemma cone_empty_source_class {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] [IsEmpty I]
    {E : BasedComplex Q (K := ℂ) I} {F : BasedComplex Q (K := ℂ) J}
    (f : Map Q E F) : classOfComplex Q (f.cone Q)=classOfComplex Q F := by
  rw [classOfComplex_reindex Q _ (Equiv.emptySum I J).symm]
  congr 1

/-- The evaluation cone of an acyclic vertex test is homotopy equivalent
 to its target. This proves the Seidel--Thomas input in the actual model. -/
theorem acyclic_twist_input : PublishedAcyclicTwist Q := by
  constructor
  intro x α hx
  induction x using Quotient.inductionOn with | _ E =>
    change classOfComplex Q (E.complex.positiveTwist Q α)=classOfComplex Q E.complex
    obtain ⟨F,hF,⟨e⟩⟩ := scalar_exact_empty_model Q (E.complex.testComplex Q α) α
      (fun _ => rfl) hx
    let := hF
    let c := e.coneSource Q (E.complex.evaluation Q α)
    exact (classOfComplex_eq Q c).symm.trans (cone_empty_source_class Q _)

end HarmonicArtin.ParabolicIntersections

end OAI
