import OAI.Topology.ArtinGroups.Coxeter.OrdinaryCoxeterMatrix
import OAI.Topology.ArtinGroups.Coxeter.PositiveBraidRelations

namespace OAI

/-! Positive braid derivations restrict to a full subdiagram. -/
namespace HarmonicArtin.ParabolicIntersections
open CoxeterExchange
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S V A : Type} (Q : ReversibleQuiver V A) (N : CoxeterMatrix S)
    (f : S → V) (hinj : Function.Injective f)
    (hN : ∀ i j, ordinaryCoxeterMatrix Q (f i) (f j)=N i j)

private lemma positive_cons (i : S) (w : List S) :
    wordPositive N (i::w)=positiveGenerator N i*wordPositive N w := rfl

include hinj hN in
/-- No braid move can introduce a vertex outside the original support.
Inside a full subdiagram every move is a defining positive Artin relation. -/
theorem positiveBraidRel_restrict [Nonempty S] {v w : List V}
    (h : PositiveBraidRel Q v w) (hv : ∀ x ∈ v, x ∈ Set.range f) :
    wordPositive N (v.map (Function.invFun f)) =
      wordPositive N (w.map (Function.invFun f)) := by
  have hinv : ∀ x, Function.invFun f (f x)=x := Function.leftInverse_invFun hinj
  induction h with
  | refl => rfl
  | symm h ih => exact (ih (h.symm.mem_set Q _ hv)).symm
  | trans h k ih ik => exact (ih hv).trans (ik (h.mem_set Q _ hv))
  | cons α h ih =>
    simp only [List.map_cons,positive_cons]
    rw [ih (fun x hx => hv x (List.mem_cons_of_mem α hx))]
  | @orthogonal α β ho w =>
    obtain ⟨i,rfl⟩ := hv α (by simp)
    obtain ⟨j,rfl⟩ := hv β (by simp)
    have hij : N i j=2 := (hN i j).symm.trans (ordinaryCoxeterMatrix_orthogonal Q ho)
    have hb := wordPositive_braid N i j
    rw [hij] at hb
    have hc : positiveGenerator N i*positiveGenerator N j =
        positiveGenerator N j*positiveGenerator N i := by
      simpa only [altList_succ,altList_zero,positive_cons,wordPositive,
        List.map_cons,List.prod_cons,List.map_nil,List.prod_nil,_root_.mul_one] using hb
    simpa only [List.map_cons,hinv,positive_cons,
      _root_.mul_assoc] using congrArg (·*wordPositive N (w.map (Function.invFun f))) hc
  | @adjacent α β edge w =>
    obtain ⟨i,rfl⟩ := hv α (by simp)
    obtain ⟨j,rfl⟩ := hv β (by simp)
    have hij : N i j=3 := (hN i j).symm.trans (ordinaryCoxeterMatrix_adjacent Q edge)
    have hb := wordPositive_braid N i j
    rw [hij] at hb
    have hc : positiveGenerator N i*(positiveGenerator N j*positiveGenerator N i) =
        positiveGenerator N j*(positiveGenerator N i*positiveGenerator N j) := by
      simpa only [altList_succ,altList_zero,positive_cons,wordPositive,
        List.map_cons,List.prod_cons,List.map_nil,List.prod_nil,_root_.mul_one] using hb
    simpa only [List.map_cons,hinv,positive_cons,
      _root_.mul_assoc] using congrArg (·*wordPositive N (w.map (Function.invFun f))) hc

end HarmonicArtin.ParabolicIntersections

end OAI
