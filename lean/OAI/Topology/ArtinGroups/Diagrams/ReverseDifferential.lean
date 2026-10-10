import Mathlib
import OAI.Topology.ArtinGroups.Diagrams.Index

namespace OAI

namespace HarmonicArtin.FiveBlock

variable {T I R : Type*} [Ring R] [Fintype T] [Fintype I]

def reverseDifferential (t r θ ι : Matrix T T R) (e : Matrix T I R)
    (d : Matrix I I R) (c : Matrix I T R) : Matrix (Index T I) (Index T I) R
  | .inl u, .inl v => -t u v
  | .inl u, .inr (.inl v) => θ u v
  | .inl u, .inr (.inr (.inl v)) => ι u v
  | .inl u, .inr (.inr (.inr (.inl j))) => e u j
  | .inr (.inl u), .inr (.inl v) => t u v
  | .inr (.inl u), .inr (.inr (.inr (.inr v))) => -ι u v
  | .inr (.inr (.inl u)), .inr (.inr (.inl v)) => t u v
  | .inr (.inr (.inl u)), .inr (.inr (.inr (.inr v))) => -r u v
  | .inr (.inr (.inr (.inl i))), .inr (.inr (.inr (.inl j))) => d i j
  | .inr (.inr (.inr (.inl i))), .inr (.inr (.inr (.inr v))) => c i v
  | .inr (.inr (.inr (.inr u))), .inr (.inr (.inr (.inr v))) => -t u v
  | _, _ => 0

def reverseProjection (e : Matrix T I R) (η : Matrix I I R) : Matrix (Index T I) I R
  | .inr (.inr (.inl u)), j => -e u j
  | .inr (.inr (.inr (.inl i))), j => η i j
  | _, _ => 0

def reverseInjection (c : Matrix I T R) (η : Matrix I I R) : Matrix I (Index T I) R
  | i, .inr (.inl u) => c i u
  | i, .inr (.inr (.inr (.inl j))) => η i j
  | _, _ => 0

def reverseHomotopy (ι : Matrix T T R) : Matrix (Index T I) (Index T I) R
  | .inr (.inr (.inl u)), .inl v => -ι u v
  | .inr (.inr (.inr (.inr u))), .inr (.inl v) => ι u v
  | _, _ => 0

lemma reverseContraction (t r θ ι : Matrix T T R) (e : Matrix T I R)
    (d η : Matrix I I R) (c : Matrix I T R)
    (hι : ι * ι = ι) (hη : η * η = η) (hit : ι * t = t) (hti : t * ι = t)
    (hri : r * ι = r) (hiθ : ι * θ = θ) (hιe : ι * e = e) (heη : e * η = e)
    (hcι : c * ι = c) (hηc : η * c = c) (hec : e * c = r + θ) :
    reverseProjection e η * reverseInjection c η = identity ι η +
      (reverseDifferential t r θ ι e d c * reverseHomotopy ι +
        reverseHomotopy ι * reverseDifferential t r θ ι e d c) := by
  ext i j
  rcases i with u | u | u | i | u <;> rcases j with v | v | v | j | v
  all_goals simp only [identity, Matrix.mul_apply, Matrix.add_apply, Fintype.sum_sum_type,
    reverseDifferential, reverseHomotopy, reverseProjection, reverseInjection, MulZeroClass.zero_mul, MulZeroClass.mul_zero,
    Finset.sum_const_zero, _root_.neg_mul, _root_.mul_neg, neg_neg,
    Finset.sum_neg_distrib, add_zero, zero_add, neg_zero]
  all_goals try simp only [← Matrix.mul_apply]
  all_goals simp only [hι, hη, hit, hti, hri, hiθ, hιe, heη, hcι, hηc, hec,
    Matrix.add_apply, neg_add, add_neg_cancel]
  all_goals try abel

end HarmonicArtin.FiveBlock

end OAI
