import Mathlib
import OAI.Topology.ArtinGroups.Model
import OAI.Topology.ArtinGroups.Quivers.ReversibleQuiver

namespace OAI

namespace HarmonicArtin.TemperleyLieb

universe u v
variable {K : Type u} [Field K]

inductive Relation (d : K) : FreeAlgebra K ℕ → FreeAlgebra K ℕ → Prop
  | square (i : ℕ) : Relation d
      (FreeAlgebra.ι K i * FreeAlgebra.ι K i) (d • FreeAlgebra.ι K i)
  | adjacent (i : ℕ) : Relation d
      (FreeAlgebra.ι K i * FreeAlgebra.ι K (i+1) * FreeAlgebra.ι K i)
      (FreeAlgebra.ι K i)
  | adjacent_rev (i : ℕ) : Relation d
      (FreeAlgebra.ι K (i+1) * FreeAlgebra.ι K i * FreeAlgebra.ι K (i+1))
      (FreeAlgebra.ι K (i+1))
  | distant (i j : ℕ) (h : i + 1 < j ∨ j + 1 < i) : Relation d
      (FreeAlgebra.ι K i * FreeAlgebra.ι K j)
      (FreeAlgebra.ι K j * FreeAlgebra.ι K i)

abbrev Algebra (d : K) := RingQuot (Relation d)

noncomputable def generator (d : K) (i : ℕ) : Algebra d :=
  RingQuot.mkAlgHom K (Relation d) (FreeAlgebra.ι K i)

lemma generator_square (d : K) (i : ℕ) :
    generator d i * generator d i = d • generator d i := by
  simpa only [generator,map_mul,map_smul] using
    (RingQuot.mkAlgHom_rel K (Relation.square (d := d) i))

lemma generator_adjacent (d : K) (i : ℕ) :
    generator d i * generator d (i+1) * generator d i = generator d i := by
  simpa only [generator,map_mul] using
    (RingQuot.mkAlgHom_rel K (Relation.adjacent (d := d) i))

lemma generator_adjacent_rev (d : K) (i : ℕ) :
    generator d (i+1) * generator d i * generator d (i+1) = generator d (i+1) := by
  simpa only [generator,map_mul] using
    (RingQuot.mkAlgHom_rel K (Relation.adjacent_rev (d := d) i))

lemma generator_distant (d : K) (i j : ℕ) (h : i + 1 < j ∨ j + 1 < i) :
    Commute (generator d i) (generator d j) := by
  change generator d i * generator d j = generator d j * generator d i
  simpa only [generator,map_mul] using
    (RingQuot.mkAlgHom_rel K (Relation.distant (d := d) i j h))

section Identities
variable {A : Type v} [Ring A] [_root_.Algebra K A]

lemma sandwich_step (p e f : A) (d r : K)
    (hp : p*p=p) (hpe : Commute p e) (he : e*e=d•e) (hef : e*f*e=e) :
    e*(p-r•(p*f*p))*e=(d-r)•(p*e) := by
  have hfirst : e*p*e=d•(p*e) := by
    rw [← hpe.eq,mul_assoc,he,mul_smul_comm]
  have hsecond : e*(p*f*p)*e=p*e := by
    calc
      e*(p*f*p)*e = p*(e*f*e)*p := by
        simp only [mul_assoc]
        rw [← hpe.eq]
        simp only [← mul_assoc]
        rw [hpe.eq]
      _ = p*e*p := by rw [hef]
      _ = p*e := by
        calc
          p*e*p = p*(p*e) := by rw [mul_assoc,← hpe.eq]
          _ = p*e := by rw [← mul_assoc,hp]
  rw [mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc,hfirst,hsecond,sub_smul]

lemma projector_step (p q e : A) (r c : K)
    (hp : p*p=p) (hqp : q*p=p) (hpq : p*q=p)
    (hqe : Commute q e) (hepe : e*p*e=c•(q*e)) (hrc : r*c=1) :
    let f := p-r•(p*e*p)
    f*f=f ∧ e*f=0 ∧ f*e=0 ∧ p*f=f ∧ f*p=f := by
  dsimp only
  have hl : p*(p-r•(p*e*p))=p-r•(p*e*p) := by
    rw [mul_sub,hp,mul_smul_comm,← mul_assoc,← mul_assoc,hp]
  have hr : (p-r•(p*e*p))*p=p-r•(p*e*p) := by
    rw [sub_mul,hp,smul_mul_assoc,mul_assoc,mul_assoc,hp]
    simp only [mul_assoc]
  have htL : e*(p*e*p)=c•(e*p) := by
    calc
      e*(p*e*p) = (e*p*e)*p := by simp only [mul_assoc]
      _ = (c•(q*e))*p := by rw [hepe]
      _ = c•(e*p) := by rw [smul_mul_assoc,hqe.eq,mul_assoc,hqp]
  have htR : (p*e*p)*e=c•(p*e) := by
    calc
      (p*e*p)*e = p*(e*p*e) := by simp only [mul_assoc]
      _ = p*(c•(q*e)) := by rw [hepe]
      _ = c•(p*e) := by rw [mul_smul_comm,← mul_assoc,hpq]
  have hkL : e*(p-r•(p*e*p))=0 := by
    rw [mul_sub,mul_smul_comm,htL,smul_smul,hrc,one_smul,sub_self]
  have hkR : (p-r•(p*e*p))*e=0 := by
    rw [sub_mul,smul_mul_assoc,htR,smul_smul,hrc,one_smul,sub_self]
  refine ⟨?_,hkL,hkR,hl,hr⟩
  have hz : (p-r•(p*e*p))*(p*e*p)=0 := by
    calc
      (p-r•(p*e*p))*(p*e*p)=((p-r•(p*e*p))*p)*e*p := by simp only [mul_assoc]
      _ = 0 := by rw [hr,hkR,zero_mul]
  rw [mul_sub,mul_smul_comm,hr,hz,smul_zero,sub_zero]

end Identities

noncomputable def projector (d : K) (r : ℕ → K) : ℕ → Algebra d
  | 0 => 1
  | n+1 => projector d r n - r (n+1) •
      (projector d r n * generator d n * projector d r n)

lemma projector_commute (d : K) (r : ℕ → K) (n k : ℕ) (h : n < k) :
    Commute (projector d r n) (generator d k) := by
  induction n with
  | zero => exact Commute.one_left _
  | succ n ih =>
    have hp := ih (by omega)
    exact hp.sub_left (((hp.mul_left
      (generator_distant d n k (Or.inl (by omega)))).mul_left hp).smul_left _)

lemma projector_absorb (d : K) (r : ℕ → K) (n : ℕ)
    (hp : projector d r n * projector d r n = projector d r n) :
    projector d r n * projector d r (n+1) = projector d r (n+1) ∧
    projector d r (n+1) * projector d r n = projector d r (n+1) := by
  simp only [projector]
  constructor
  · rw [mul_sub,hp,mul_smul_comm,← mul_assoc,← mul_assoc,hp]
  · rw [sub_mul,hp,smul_mul_assoc,mul_assoc,mul_assoc,hp]
    simp only [mul_assoc]

lemma projector_properties (d : K) (r : ℕ → K) (N : ℕ) (hr0 : r 0 = 0)
    (hr : ∀ n < N, r (n+1) * (d-r n) = 1) :
    ∀ n ≤ N,
      projector d r n * projector d r n = projector d r n ∧
      (∀ i < n, generator d i * projector d r n = 0 ∧
        projector d r n * generator d i = 0) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    cases n with
    | zero => simp [projector]
    | succ n =>
      have hp := ih n (by omega) (by omega)
      let p := projector d r n
      let q := match n with
        | 0 => (1 : Algebra d)
        | k+1 => projector d r k
      have hqp : q*p=p ∧ p*q=p := by
        cases n with
        | zero => simp [p,q,projector]
        | succ k => exact projector_absorb d r k (ih k (by omega) (by omega)).1
      have hqe : Commute q (generator d n) := by
        cases n with
        | zero => exact Commute.one_left _
        | succ k => exact projector_commute d r k (k+1) (by omega)
      have hsand : generator d n * p * generator d n =
          (d-r n) • (q * generator d n) := by
        cases n with
        | zero => simpa [p,q,projector,hr0] using generator_square d 0
        | succ k =>
          exact sandwich_step (projector d r k) (generator d (k+1))
            (generator d k) d (r (k+1))
            (ih k (by omega) (by omega)).1
            (projector_commute d r k (k+1) (by omega))
            (generator_square d (k+1)) (generator_adjacent_rev d k)
      have hstep := projector_step p q (generator d n) (r (n+1)) (d-r n)
        hp.1 hqp.1 hqp.2 hqe hsand (hr n (by omega))
      refine ⟨hstep.1, ?_⟩
      intro i hi
      rcases eq_or_lt_of_le (Nat.le_of_lt_succ hi) with rfl | hin
      · exact ⟨hstep.2.1,hstep.2.2.1⟩
      · have hk := hp.2 i hin
        constructor
        · simp only [projector,mul_sub,mul_smul_comm,← mul_assoc,hk.1,
            zero_mul,smul_zero,sub_self]
        · simp only [projector,sub_mul,smul_mul_assoc,mul_assoc,hk.2,
            mul_zero,smul_zero,sub_self]

noncomputable def augmentation (d : K) : Algebra d →ₐ[K] K :=
  RingQuot.liftAlgHom K ⟨FreeAlgebra.lift K (fun _ : ℕ => (0 : K)), by
    intro a b h
    cases h <;> simp⟩

@[simp] lemma augmentation_generator (d : K) (i : ℕ) :
    augmentation d (generator d i) = 0 := by
  simp only [augmentation,generator,RingQuot.liftAlgHom_mkAlgHom_apply,
    FreeAlgebra.lift_ι_apply]

@[simp] lemma augmentation_projector (d : K) (r : ℕ → K) (n : ℕ) :
    augmentation d (projector d r n) = 1 := by
  induction n with
  | zero => simp [projector]
  | succ n ih => simp [projector,ih]

lemma projector_ne_zero (d : K) (r : ℕ → K) (n : ℕ) :
    projector d r n ≠ 0 := by
  intro h
  have := augmentation_projector d r n
  rw [h,map_zero] at this
  exact zero_ne_one this

noncomputable def strands (d : K) (n : ℕ) : Subalgebra K (Algebra d) :=
  _root_.Algebra.adjoin K (generator d '' {i | i < n})

lemma strands_mono (d : K) {n k : ℕ} (hnk : n ≤ k) :
    strands d n ≤ strands d k := by
  exact _root_.Algebra.adjoin_mono (Set.image_mono (by intro i hi; exact lt_of_lt_of_le hi hnk))

lemma generator_mem_strands (d : K) {i n : ℕ} (hi : i < n) :
    generator d i ∈ strands d n :=
  _root_.Algebra.subset_adjoin ⟨i,hi,rfl⟩

lemma projector_mem_strands (d : K) (r : ℕ → K) (n : ℕ) :
    projector d r n ∈ strands d n := by
  induction n with
  | zero => exact (strands d 0).one_mem
  | succ n ih =>
    have hp := strands_mono d (Nat.le_succ n) ih
    exact (strands d (n+1)).sub_mem hp ((strands d (n+1)).smul_mem
      ((strands d (n+1)).mul_mem
        ((strands d (n+1)).mul_mem hp (generator_mem_strands d (by omega))) hp) _)

lemma turnback_scalar_action (d : K) (n : ℕ) (p : Algebra d)
    (hp : ∀ i < n, generator d i*p=0 ∧ p*generator d i=0)
    {x : Algebra d} (hx : x ∈ strands d n) :
    p*x=augmentation d x • p ∧ x*p=augmentation d x • p := by
  induction hx using _root_.Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i,hi,rfl⟩ := hx
    simpa using (hp i hi).symm
  | algebraMap c =>
    simp [_root_.Algebra.algebraMap_eq_smul_one]
  | add x y hx hy ihx ihy =>
    rw [map_add,add_smul,mul_add,add_mul,ihx.1,ihy.1,ihx.2,ihy.2]
    exact ⟨rfl,rfl⟩
  | mul x y hx hy ihx ihy =>
    constructor
    · rw [← mul_assoc,ihx.1,smul_mul_assoc,ihy.1,smul_smul,map_mul]
    · rw [mul_assoc,ihy.2,mul_smul_comm,ihx.2,smul_smul,map_mul,mul_comm]

lemma turnback_projector_unique (d : K) (n : ℕ) (p q : Algebra d)
    (hpm : p ∈ strands d n) (hqm : q ∈ strands d n)
    (hp : ∀ i < n, generator d i*p=0 ∧ p*generator d i=0)
    (hq : ∀ i < n, generator d i*q=0 ∧ q*generator d i=0)
    (hap : augmentation d p=1) (haq : augmentation d q=1) : p=q := by
  have h1 := (turnback_scalar_action d n p hp hqm).1
  have h2 := (turnback_scalar_action d n q hq hpm).2
  rw [haq,one_smul] at h1
  rw [hap,one_smul] at h2
  exact h1.symm.trans h2

end HarmonicArtin.TemperleyLieb

end OAI
