import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.SphericalLongest

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] (M:CoxeterMatrix S)

lemma positiveSimpleLift_prefix_longest (T:Set S) (q:M.Group) (hq:IsParabolicLongest M T q)
    (w:M.Group) (hw:w∈coxeterParabolic M T) :
    PositivePrefix M (positiveSimpleLift M w) (positiveSimpleLift M q) := by
  have hh:=parabolic_longest_length_mul M T q hq w hw
  have he:M.toCoxeterSystem.length (w⁻¹*q)=M.toCoxeterSystem.length (q*w):=by
    have h:=M.toCoxeterSystem.length_inv (q*w)
    rw [mul_inv_rev,parabolic_longest_inverse M T q hq] at h
    exact h
  refine ⟨positiveSimpleLift M (w⁻¹*q),?_⟩
  have hlen:M.toCoxeterSystem.length (w*(w⁻¹*q))=
      M.toCoxeterSystem.length w+M.toCoxeterSystem.length (w⁻¹*q):=by
    rw [mul_inv_cancel_left,he]
    omega
  simpa only [mul_inv_cancel_left] using positiveSimpleLift_mul M w (w⁻¹*q) hlen

abbrev PositiveLiftedCell := PositiveArtin M × SphericalType M

def positiveCellToLifted (a:PositiveLiftedCell M) : LiftedCell M :=
  (positiveToArtin M a.1,a.2)

noncomputable def positiveCellTop (a:PositiveLiftedCell M) : PositiveArtin M :=
  a.1*positiveSimpleLift M (sphericalLongest M a.2)

lemma positiveCellTop_toArtin (a:PositiveLiftedCell M) :
    positiveToArtin M (positiveCellTop M a)=liftedTopVertex M (positiveCellToLifted M a) := by
  simp only [positiveCellTop,map_mul,positiveToArtin_simpleLift,liftedTopVertex,positiveCellToLifted]

theorem positiveCellTop_prefix_of_face
    (inj:Function.Injective (positiveToArtin M)) (a b:PositiveLiftedCell M)
    (h:LiftedFace M (positiveCellToLifted M a) (positiveCellToLifted M b)) :
    PositivePrefix M (positiveCellTop M a) (positiveCellTop M b) := by
  obtain ⟨hAB,u,hu,hr,hmin,he⟩:=h
  have hr':M.toCoxeterSystem.IsReduced u:=hr
  have ha:a.1=b.1*wordPositive M u:=by
    apply inj
    simpa only [map_mul,positiveToArtin_word,positiveCellToLifted] using he
  let v:=wordCoxeter M u*sphericalLongest M a.2
  have hlen:M.toCoxeterSystem.length v=M.toCoxeterSystem.length (wordCoxeter M u)+
      M.toCoxeterSystem.length (sphericalLongest M a.2):=by
    apply length_mul_of_right_minimum M.toCoxeterSystem a.2.val (wordCoxeter M u)
    · intro x hx
      exact hmin ⟨x,hx⟩
    · exact (sphericalLongest_spec M a.2).1
  have hv:v∈coxeterParabolic M b.2.val:=(coxeterParabolic M b.2.val).mul_mem
    (wordCoxeter_mem_parabolic M _ u hu)
    (coxeterParabolic_mono M hAB (sphericalLongest_spec M a.2).1)
  obtain ⟨r,heq⟩:=positiveSimpleLift_prefix_longest M _ _ (sphericalLongest_spec M b.2) v hv
  have hu':wordPositive M u=positiveSimpleLift M (wordCoxeter M u):=(positiveSimpleLift_word M u hr').symm
  have ha':positiveCellTop M a=b.1*positiveSimpleLift M v:=by
    change a.1*positiveSimpleLift M (sphericalLongest M a.2)=_
    rw [ha,hu',mul_assoc,←positiveSimpleLift_mul M _ _ hlen]
  refine ⟨r,?_⟩
  change b.1*positiveSimpleLift M (sphericalLongest M b.2)=_
  rw [ha',heq,mul_assoc]

lemma positiveCellTop_degree_mono
    (inj:Function.Injective (positiveToArtin M)) (a b:PositiveLiftedCell M)
    (h:positiveCellToLifted M a≤positiveCellToLifted M b) :
    positiveDegree M (positiveCellTop M a)≤positiveDegree M (positiveCellTop M b) :=
  positivePrefix_degree M (positiveCellTop_prefix_of_face M inj a b ((lifted_le_iff_face M _ _).mp h))

lemma positiveCellTop_degree_strict
    (inj:Function.Injective (positiveToArtin M)) (a b:PositiveLiftedCell M)
    (h:positiveCellToLifted M a≤positiveCellToLifted M b)
    (hne:positiveCellTop M a≠positiveCellTop M b) :
    positiveDegree M (positiveCellTop M a)<positiveDegree M (positiveCellTop M b) := by
  have hp:=positiveCellTop_prefix_of_face M inj a b ((lifted_le_iff_face M _ _).mp h)
  exact lt_of_le_of_ne (positivePrefix_degree M hp)
    (fun he=>hne (positivePrefix_eq_of_degree M hp he))

end HarmonicArtin

end OAI
