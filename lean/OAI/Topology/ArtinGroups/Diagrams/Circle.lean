import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.QuantumNumber
import OAI.Topology.ArtinGroups.Diagrams.Relation

namespace OAI

namespace HarmonicArtin.TemperleyLieb

noncomputable def circle (m : ℕ) : ℂ := (2 * Real.cos (Real.pi / m) : ℝ)

noncomputable def quantumRatio (m : ℕ) (n : ℕ) : ℂ :=
  (quantumNumber m n / quantumNumber m (n+1) : ℝ)

lemma quantumRatio_zero (m : ℕ) : quantumRatio m 0 = 0 := by
  simp [quantumRatio,quantumNumber_zero]

lemma quantumRatio_reciprocal {m : ℕ} (hm : 2 ≤ m) (n : ℕ) (hn : n+2 < m) :
    quantumRatio m (n+1) * (circle m - quantumRatio m n) = 1 := by
  have h1 : quantumNumber m ((n:ℤ)+1) ≠ 0 :=
    ne_of_gt (quantumNumber_pos hm (by omega) (by omega))
  have h2 : quantumNumber m ((n:ℤ)+2) ≠ 0 :=
    ne_of_gt (quantumNumber_pos hm (by omega) (by omega))
  have hrec : quantumNumber m n + quantumNumber m ((n:ℤ)+2) =
      (2*Real.cos (Real.pi/m))*quantumNumber m ((n:ℤ)+1) := by
    have ha : (n:ℤ)+1-1=(n:ℤ) := by omega
    have hb : (n:ℤ)+1+1=(n:ℤ)+2 := by omega
    simpa only [ha,hb] using quantumNumber_recurrence m ((n:ℤ)+1)
  have hreal : (quantumNumber m ((n:ℤ)+1) / quantumNumber m ((n:ℤ)+2)) *
      ((2*Real.cos (Real.pi/m))-quantumNumber m n / quantumNumber m ((n:ℤ)+1)) = 1 := by
    field_simp
    nlinarith
  unfold quantumRatio circle
  push_cast
  have hc := congrArg (fun x : ℝ => (x : ℂ)) hreal
  push_cast at hc
  convert hc using 1
  congr 1

noncomputable def jonesWenzl (m n : ℕ) : Algebra (circle m) :=
  projector (circle m) (quantumRatio m) n

lemma jonesWenzl_properties {m : ℕ} (hm : 2 ≤ m) {n : ℕ} (hn : n+2 ≤ m) :
    jonesWenzl m n * jonesWenzl m n = jonesWenzl m n ∧
    (∀ i < n, generator (circle m) i*jonesWenzl m n=0 ∧
      jonesWenzl m n*generator (circle m) i=0) := by
  exact projector_properties (circle m) (quantumRatio m) (m-2)
    (quantumRatio_zero m) (fun k hk => quantumRatio_reciprocal hm k (by omega)) n (by omega)

lemma jonesWenzl_ne_zero (m n : ℕ) : jonesWenzl m n ≠ 0 :=
  projector_ne_zero (circle m) (quantumRatio m) n

lemma jonesWenzl_corner {m : ℕ} (hm : 2 ≤ m) {n : ℕ} (hn : n+2 ≤ m)
    (x : Algebra (circle m)) (hx : x ∈ strands (circle m) n) :
    jonesWenzl m n * x * jonesWenzl m n =
      augmentation (circle m) x • jonesWenzl m n := by
  have hp := jonesWenzl_properties hm hn
  rw [(turnback_scalar_action (circle m) n (jonesWenzl m n) hp.2 hx).1,
    smul_mul_assoc,hp.1]

end HarmonicArtin.TemperleyLieb

end OAI
