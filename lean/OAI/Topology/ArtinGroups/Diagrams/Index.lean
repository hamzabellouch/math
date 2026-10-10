import Mathlib
import OAI.Topology.ArtinGroups.Quivers.ReversibleQuiver

namespace OAI

namespace HarmonicArtin.FiveBlock

variable {T I R : Type*} [Ring R] [Fintype T] [Fintype I]

abbrev Index (T I : Type*) := T ⊕ T ⊕ T ⊕ I ⊕ T

def differential (t r θ ι : Matrix T T R) (e : Matrix T I R)
    (d : Matrix I I R) (c : Matrix I T R) : Matrix (Index T I) (Index T I) R
  | .inl u, .inl v => -t u v
  | .inl u, .inr (.inl v) => -r u v
  | .inl u, .inr (.inr (.inl v)) => -ι u v
  | .inl u, .inr (.inr (.inr (.inl j))) => e u j
  | .inr (.inl u), .inr (.inl v) => t u v
  | .inr (.inl u), .inr (.inr (.inr (.inr v))) => ι u v
  | .inr (.inr (.inl u)), .inr (.inr (.inl v)) => t u v
  | .inr (.inr (.inl u)), .inr (.inr (.inr (.inr v))) => θ u v
  | .inr (.inr (.inr (.inl i))), .inr (.inr (.inr (.inl j))) => d i j
  | .inr (.inr (.inr (.inl i))), .inr (.inr (.inr (.inr v))) => c i v
  | .inr (.inr (.inr (.inr u))), .inr (.inr (.inr (.inr v))) => -t u v
  | _, _ => 0

def projection (e : Matrix T I R) (η : Matrix I I R) : Matrix (Index T I) I R
  | .inr (.inr (.inl u)), j => e u j
  | .inr (.inr (.inr (.inl i))), j => η i j
  | _, _ => 0

def injection (c : Matrix I T R) (η : Matrix I I R) : Matrix I (Index T I) R
  | i, .inr (.inl u) => -c i u
  | i, .inr (.inr (.inr (.inl j))) => η i j
  | _, _ => 0

def homotopy (ι : Matrix T T R) : Matrix (Index T I) (Index T I) R
  | .inr (.inr (.inl u)), .inl v => ι u v
  | .inr (.inr (.inr (.inr u))), .inr (.inl v) => -ι u v
  | _, _ => 0

def identity (ι : Matrix T T R) (η : Matrix I I R) : Matrix (Index T I) (Index T I) R
  | .inl u, .inl v => ι u v
  | .inr (.inl u), .inr (.inl v) => ι u v
  | .inr (.inr (.inl u)), .inr (.inr (.inl v)) => ι u v
  | .inr (.inr (.inr (.inl i))), .inr (.inr (.inr (.inl j))) => η i j
  | .inr (.inr (.inr (.inr u))), .inr (.inr (.inr (.inr v))) => ι u v
  | _, _ => 0

lemma contraction (t r θ ι : Matrix T T R) (e : Matrix T I R)
    (d η : Matrix I I R) (c : Matrix I T R)
    (hι : ι * ι = ι) (hη : η * η = η) (hit : ι * t = t) (hti : t * ι = t)
    (hir : ι * r = r) (hθi : θ * ι = θ) (hιe : ι * e = e) (heη : e * η = e)
    (hcι : c * ι = c) (hηc : η * c = c) (hec : e * c = r + θ) :
    projection e η * injection c η = identity ι η +
      (differential t r θ ι e d c * homotopy ι +
        homotopy ι * differential t r θ ι e d c) := by
  ext i j
  rcases i with u | u | u | i | u <;> rcases j with v | v | v | j | v
  all_goals simp only [identity, Matrix.mul_apply, Matrix.add_apply, Fintype.sum_sum_type,
    differential, homotopy, projection, injection, MulZeroClass.zero_mul, MulZeroClass.mul_zero,
    Finset.sum_const_zero, _root_.neg_mul, _root_.mul_neg, neg_neg,
    Finset.sum_neg_distrib, add_zero, zero_add, neg_zero]
  all_goals try simp only [← Matrix.mul_apply]
  all_goals simp only [hι, hη, hit, hti, hir, hθi, hιe, heη, hcι, hηc, hec,
    Matrix.add_apply, neg_add, add_neg_cancel]
  exact add_comm _ _

end HarmonicArtin.FiveBlock

end OAI
