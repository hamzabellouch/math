import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.IntegralRowReflect

namespace OAI

namespace HarmonicArtin
open Matrix
open scoped Matrix BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {V:Type*} [Fintype V] [DecidableEq V]

lemma integralRowReflect_apply_ne (C:Matrix V V ℤ) (i j:V) (h:j≠i) (x:V → ℤ) :
    integralRowReflect C i x j=x j := by
  simp [integralRowReflect,h]

theorem integral_root_sign_flip (C:Matrix V V ℤ) (hd:∀ i,C i i=2)
    (x:V → ℤ) (hx:integralQuadratic C x=2) (hpos:∀ j,0 ≤ x j)
    (i:V) (hneg:∀ j,integralRowReflect C i x j ≤ 0) : x=Pi.single i 1 := by
  have hz:∀ j,j≠i → x j=0 := by
    intro j hji
    have hj:=hneg j
    rw [integralRowReflect_apply_ne C i j hji x] at hj
    exact le_antisymm hj (hpos j)
  have he:x=Pi.single i (x i) := by
    ext j
    by_cases hji:j=i
    · subst j
      simp
    · simp [hji,hz j hji]
  have hn:2*x i*x i=2 := by
    conv_lhs at hx => rw [he]
    simpa [integralQuadratic,Pi.single_apply,hd] using hx
  have hi:x i=1 := by
    have hp:=hpos i
    nlinarith [sq_nonneg (x i-1)]
  rw [he,hi]

theorem integral_positive_root_reflect (C:Matrix V V ℤ) (hs:∀ i j,C i j=C j i)
    (hd:∀ i,C i i=2) (hoff:∀ i j,i≠j → C i j ≤ 0)
    (hp:(C.map (Int.cast:ℤ → ℝ)).PosDef) (w:List V) (a i:V)
    (hpos:∀ j,0 ≤ integralReflectWord C w (Pi.single a 1) j)
    (hne:integralReflectWord C w (Pi.single a 1)≠Pi.single i 1) :
    ∀ j,0 ≤ integralRowReflect C i (integralReflectWord C w (Pi.single a 1)) j := by
  rcases integralReflectWord_sign C hs hd hoff hp (i::w) a with h|h
  · exact h
  · exact (hne (integral_root_sign_flip C hd _
      (integralReflectWord_norm C hs hd w a) hpos i h)).elim

end HarmonicArtin

end OAI
