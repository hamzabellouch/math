import Mathlib
import OAI.Topology.ArtinGroups.Coxeter.BraidCoreFirstTarget

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
variable {V B K : Type*} (Q : ReversibleQuiver V B)
  [Field K] [Fintype V] [Fintype B] [DecidableEq V] [DecidableEq B]

lemma vertexId_mul_pathBasis (v : V) (p : Path V B) :
    vertexId Q v * pathBasis Q (K := K) p =
      if Path.source Q p = v then pathBasis Q p else 0 := by
  apply (pathCoordinates Q).injective
  funext q
  rw [coordinates_vertexId_left]
  by_cases h : Path.source Q p=v
  · rw [ite_eq_left h]
    by_cases hpq : p=q
    · subst q; rw [ite_eq_left h]
    · simp [pathBasis_coordinates,hpq]
  · rw [ite_eq_right h, map_zero]
    by_cases hpq : p=q
    · subst q; simp [h]
    · simp [pathBasis_coordinates,hpq]

lemma pathBasis_mul_vertexId (v : V) (p : Path V B) :
    pathBasis Q (K := K) p * vertexId Q v =
      if Path.target Q p = v then pathBasis Q p else 0 := by
  apply (pathCoordinates Q).injective
  funext q
  rw [coordinates_vertexId_right]
  by_cases h : Path.target Q p=v
  · rw [ite_eq_left h]
    by_cases hpq : p=q
    · subst q; rw [ite_eq_left h]
    · simp [pathBasis_coordinates,hpq]
  · rw [ite_eq_right h, map_zero]
    by_cases hpq : p=q
    · subst q; simp [h]
    · simp [pathBasis_coordinates,hpq]

omit [Fintype V] in
lemma arrowBasis_mul_arrowBasis (a b : B) :
    arrowBasis Q (K := K) a * arrowBasis Q b =
      if Q.reverse a = b then tokenBasis Q (Q.source a) else 0 := by
  by_cases hr : Q.reverse a=b
  · subst b
    rw [ite_eq_left rfl]
    exact BasedComplex.arrowBasis_reverse Q a
  · rw [ite_eq_right hr]
    apply Zigzag.ext
    · rw [vertex_mul, vertex_zero]
      funext v
      simp [arrowBasis,vertex]
    · rw [arrow_mul, arrow_zero]
      funext e
      simp [arrowBasis,vertex,arrow,leftScale,rightScale]
    · rw [token_mul, token_zero]
      funext v
      simp only [arrowBasis,vertex,arrow,token,
        Pi.add_apply,Pi.mul_apply,Pi.zero_apply]
      simp only [backtrack,Pi.single_apply]
      rw [Finset.sum_eq_single a]
      · simp [hr]
      · intro e he hea
        simp [hea]
      · simp

omit [DecidableEq B] in
lemma map_mul_of_pathBasis {R : Type*} [Ring R] [Algebra K R]
    (f : Q.Zigzag K →ₗ[K] R)
    (hf : ∀ p q, f (pathBasis Q p * pathBasis Q q)=f (pathBasis Q p)*f (pathBasis Q q))
    (x y : Q.Zigzag K) : f (x*y)=f x*f y := by
  conv_lhs => rw [← sum_pathBasis Q x, ← sum_pathBasis Q y]
  conv_rhs => rw [← sum_pathBasis Q x, ← sum_pathBasis Q y]
  simp only [Finset.sum_mul,Finset.mul_sum,smul_mul_assoc,
    map_sum,map_smul,hf,Algebra.mul_smul_comm]

end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
