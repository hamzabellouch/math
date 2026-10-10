import OAI.RingTheory.DirectFiniteness.Model

namespace OAI

/-- A Lucas–Lehmer certificate for the Mersenne prime used in the degree bound. -/
theorem mersenne_21701_prime : (mersenne 21701).Prime := by
  apply lucas_lehmer_sufficiency
  · norm_num
  · norm_num

end OAI
