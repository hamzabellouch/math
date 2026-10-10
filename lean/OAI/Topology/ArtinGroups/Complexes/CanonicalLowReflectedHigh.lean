import Mathlib
import OAI.Topology.ArtinGroups.Complexes.TotalVector

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

theorem canonicalLow_reflected_high (hn:∀ a,Q.source a≠Q.target a)
    (w:List V) (q:ℤ) (x:FiniteHomotopyClass Q (K:=K))
    (hlo:ClassLowerBound Q q x) (hhi:ClassUpperBound Q q x)
    (hl:ClassLowerBound Q q (canonicalWordLow Q w q x))
    (hh:ClassUpperBound Q q (canonicalWordLow Q w q x)) :
    classTotalVector Q (classLayer Q q (inverseWordAction Q w x))=
      rowReflectWord (unfoldedCartan Q) w.reverse
        (classTotalVector Q x-classTotalVector Q (canonicalWordLow Q w q x)) := by
  have h:=canonicalLow_reflected_high_signed Q hn w q x hhi
  have lower : ClassLowerBound Q q (classLayer Q q (inverseWordAction Q w x)) :=
    classLowerBound_of_representative Q _ (fun index => le_of_eq index.property.symm)
  have upper : ClassUpperBound Q q (classLayer Q q (inverseWordAction Q w x)) :=
    classUpperBound_of_representative Q _ (fun index => le_of_eq index.property)
  rw [classSignedVector_pure Q _ q lower upper,
    classSignedVector_pure Q x q hlo hhi,classSignedVector_pure Q _ q hl hh,
    ← smul_sub,rowReflectWord_smul] at h
  have h':=congrArg (fun z:V→ℝ=>cochainSign (K:=ℝ) q • z) h
  simpa only [smul_smul,cochainSign_mul_self,one_smul] using h'

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
