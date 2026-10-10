import Mathlib
import OAI.Topology.ArtinGroups.Quivers.TraceLinear

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I J L : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V] [Fintype I] [Fintype J] [Fintype L]

lemma homSpace_mul {E : BasedComplex Q (K := K) I} {F : BasedComplex Q (K := K) J}
    {G : BasedComplex Q (K := K) L} {n m v w : ℤ}
    {f : Matrix I J (Q.Zigzag K)} {g : Matrix J L (Q.Zigzag K)}
    (hf : f ∈ homSpace Q E F n v) (hg : g ∈ homSpace Q F G m w) :
    f * g ∈ homSpace Q E G (n + m) (v + w) :=
  ⟨projectiveEntries_mul Q hf.1 hg.1, mapDegree_mul Q hf.2 hg.2⟩

lemma homDifferential_mul (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (G : BasedComplex Q (K := K) L)
    (n m : ℤ) (f : Matrix I J (Q.Zigzag K)) (g : Matrix J L (Q.Zigzag K)) :
    homDifferential Q E G (n + m) (f * g) =
      homDifferential Q E F n f * g +
        cochainSign (K := K) n • (f * homDifferential Q F G m g) := by
  change E.differential * (f * g) - cochainSign (K := K) (n + m) • (f * g * G.differential) =
    (E.differential * f - cochainSign (K := K) n • (f * F.differential)) * g +
      cochainSign (K := K) n • (f * (F.differential * g - cochainSign (K := K) m • (g * G.differential)))
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    smul_sub, smul_smul, cochainSign_add, Matrix.mul_assoc]
  abel

lemma homCycles_mul {E : BasedComplex Q (K := K) I} {F : BasedComplex Q (K := K) J}
    {G : BasedComplex Q (K := K) L} {n m v w : ℤ}
    {f : Matrix I J (Q.Zigzag K)} {g : Matrix J L (Q.Zigzag K)}
    (hf : f ∈ homCycles Q E F n v) (hg : g ∈ homCycles Q F G m w) :
    f * g ∈ homCycles Q E G (n + m) (v + w) := by
  refine ⟨homSpace_mul Q hf.1 hg.1, ?_⟩
  change homDifferential Q E G (n + m) (f * g) = 0
  rw [homDifferential_mul Q E F G n m,
    show homDifferential Q E F n f = 0 from hf.2,
    show homDifferential Q F G m g = 0 from hg.2,
    Matrix.zero_mul, Matrix.mul_zero, smul_zero, add_zero]

lemma homBoundary_mul_cycle {E : BasedComplex Q (K := K) I}
    {F : BasedComplex Q (K := K) J} {G : BasedComplex Q (K := K) L}
    {n m v w : ℤ} {f : Matrix I J (Q.Zigzag K)} {g : Matrix J L (Q.Zigzag K)}
    (hf : f ∈ homBoundaries Q E F n v) (hg : g ∈ homCycles Q F G m w) :
    f * g ∈ homBoundaries Q E G (n + m) (v + w) := by
  obtain ⟨h, hh, rfl⟩ := hf
  refine ⟨h * g, ?_, ?_⟩
  · have hm := homSpace_mul Q hh hg.1
    have he : n + m - 1 = n - 1 + m := by omega
    change h * g ∈ homSpace Q E G (n + m - 1) (v + w)
    rw [he]
    exact hm
  · convert homDifferential_mul Q E F G (n - 1) m h g using 1
    · congr 2; omega
    · rw [show homDifferential Q F G m g = 0 from hg.2,
        Matrix.mul_zero, smul_zero, add_zero]

lemma homCycle_mul_boundary {E : BasedComplex Q (K := K) I}
    {F : BasedComplex Q (K := K) J} {G : BasedComplex Q (K := K) L}
    {n m v w : ℤ} {f : Matrix I J (Q.Zigzag K)} {g : Matrix J L (Q.Zigzag K)}
    (hf : f ∈ homCycles Q E F n v) (hg : g ∈ homBoundaries Q F G m w) :
    f * g ∈ homBoundaries Q E G (n + m) (v + w) := by
  obtain ⟨h, hh, rfl⟩ := hg
  refine ⟨cochainSign (K := K) n • (f * h), ?_, ?_⟩
  · have hm := (homSpace Q E G (n + (m - 1)) (v + w)).smul_mem
      (cochainSign (K := K) n) (homSpace_mul Q hf.1 hh)
    have he : n + m - 1 = n + (m - 1) := by omega
    change cochainSign (K := K) n • (f * h) ∈ homSpace Q E G (n + m - 1) (v + w)
    rw [he]
    exact hm
  · rw [map_smul]
    have hm := homDifferential_mul Q E F G n (m - 1) f h
    have he : n + m - 1 = n + (m - 1) := by omega
    rw [he, hm, show homDifferential Q E F n f = 0 from hf.2,
      Matrix.zero_mul, zero_add, smul_smul, cochainSign_mul_self, one_smul]

lemma map_mem_homCycles {E : BasedComplex Q (K := K) I}
    {F : BasedComplex Q (K := K) J} (f : Map Q E F) :
    f.matrix ∈ homCycles Q E F 0 0 := by
  refine ⟨⟨f.entries, f.degree⟩, ?_⟩
  change E.differential * f.matrix - cochainSign (K := K) 0 •
    (f.matrix * F.differential) = 0
  rw [cochainSign_zero, one_smul, f.commute, sub_self]

lemma homotopyEquation_boundary {E : BasedComplex Q (K := K) I}
    {f : Matrix I I (Q.Zigzag K)} {h : Matrix I I (Q.Zigzag K)}
    (hh : h ∈ homSpace Q E E (-1) 0)
    (he : f = E.differential * h + h * E.differential) :
    f ∈ homBoundaries Q E E 0 0 := by
  refine ⟨h, hh, ?_⟩
  change E.differential * h - cochainSign (K := K) (-1) • (h * E.differential) = f
  have hs : cochainSign (K := K) (-1) = -1 := by
    rw [cochainSign_neg, show (1 : ℤ) = 0 + 1 by rfl, cochainSign_add_one, cochainSign_zero]
  rw [hs, neg_one_smul, sub_neg_eq_add, he]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
