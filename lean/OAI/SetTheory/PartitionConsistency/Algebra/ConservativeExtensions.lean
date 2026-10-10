import Mathlib
import OAI.SetTheory.PartitionConsistency.Algebra.ProbeMargins
import OAI.SetTheory.PartitionConsistency.Algebra.MergerCones

namespace OAI

namespace PartitionConsistency.DiagramOrder
universe u v w

/-- Conservation of a submonoid means more than an injective homomorphism:
right factors of old comparisons, entire old intersections, and absence of
old common right multiples are preserved. -/
structure Conservative {M : Type u} {N : Type v} [Monoid M] [Monoid N]
    (f : M →* N) : Prop where
  injective : Function.Injective f
  factors : ∀ x y : M, ∀ z : N, f x * z = f y → ∃ t : M, f t = z
  intersections : ∀ x y j : M, (∀ z : M, x ∣ z ∧ y ∣ z ↔ j ∣ z) →
    ∀ z : N, f x ∣ z ∧ f y ∣ z ↔ f j ∣ z
  common : ∀ x y : M, (∃ z : N, f x ∣ z ∧ f y ∣ z) →
    ∃ z : M, x ∣ z ∧ y ∣ z

namespace Conservative
variable {M : Type u} {N : Type v} {R : Type w} [Monoid M] [Monoid N] [Monoid R]
  {f : M →* N} (hf : Conservative f)

include hf

/-- Division is reflected together with its particular unique factor,
not by an unrelated witness to the existence of a comparison. -/
theorem factor_eq {x y : M} {z : N} (h : f x * z = f y) :
    ∃ t : M, f t = z ∧ x * t = y := by
  obtain ⟨t, ht⟩ := hf.factors x y z h
  exact ⟨t, ht, hf.injective (by rw [f.map_mul, ht, h])⟩

theorem dvd_iff (x y : M) : f x ∣ f y ↔ x ∣ y := by
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨t, _, ht⟩ := hf.factor_eq hz.symm
    exact ⟨t, ht.symm⟩
  · exact f.map_dvd

theorem common_iff (x y : M) :
    (∃ z : N, f x ∣ z ∧ f y ∣ z) ↔ ∃ z : M, x ∣ z ∧ y ∣ z := by
  constructor
  · exact hf.common x y
  · rintro ⟨z, hxz, hyz⟩
    exact ⟨f z, f.map_dvd hxz, f.map_dvd hyz⟩

theorem intersection_iff (x y j : M) :
    (∀ z : N, f x ∣ z ∧ f y ∣ z ↔ f j ∣ z) ↔
      (∀ z : M, x ∣ z ∧ y ∣ z ↔ j ∣ z) := by
  constructor
  · intro h z
    simpa only [hf.dvd_iff] using h (f z)
  · exact hf.intersections x y j

/-- The composition law is what makes comparisons testable in the final
monoid, independently of the birth step at which a factor was computed. -/
theorem comp {g : N →* R} (hg : Conservative g) : Conservative (g.comp f) where
  injective := hg.injective.comp hf.injective
  factors x y z h := by
    obtain ⟨t, ht, he⟩ := hg.factor_eq h
    obtain ⟨s, hs⟩ := hf.factors x y t he
    exact ⟨s, by change g (f s) = z; rw [hs, ht]⟩
  intersections x y j hj := hg.intersections (f x) (f y) (f j) (hf.intersections x y j hj)
  common x y h := hf.common x y (hg.common (f x) (f y) h)

omit hf in
/-- Identity inclusions are conservative. -/
theorem id (M : Type u) [Monoid M] : Conservative (MonoidHom.id M) where
  injective := Function.injective_id
  factors _ _ z _ := ⟨z, rfl⟩
  intersections _ _ _ h := h
  common _ _ h := h

end Conservative
end PartitionConsistency.DiagramOrder

namespace PartitionConsistency.ProbeAlgebra.Path
universe u
open DiagramOrder
variable {M : Type u} [LeftCancelMonoid M] [IsConical M] {a e : M}
  (P : Path M a) (he : e ≠ 1) (b : M)

/-- All four conservation requirements for the actual probe extension. -/
theorem oldHom_conservative : Conservative (Word.oldHom (P.alphabet he) b) where
  injective := Word.oldHom_injective _ _
  factors x y z hz := by
    obtain ⟨t, ht, _⟩ := (Word.old_mul_eq_old_iff (P.alphabet he) b x y z).1 hz
    exact ⟨t, ht.symm⟩
  intersections := P.old_cone_intersection he b
  common _ _ h := by
    obtain ⟨z, hx, hy⟩ := h
    exact P.common_multiple_reflection he b hx hy

end PartitionConsistency.ProbeAlgebra.Path

namespace PartitionConsistency.MergerAlgebra.Word
universe u v
open DiagramOrder
variable {M : Type u} {D : Type v} [Monoid M] [RightFreeAction M D]

/-- All four conservation requirements for merger normal forms. -/
theorem oldHom_conservative : Conservative (oldHom : M →* Word M D) where
  injective := oldHom_injective
  factors x y z hz := by
    obtain ⟨_, t, _, ht, _⟩ := factors_of_old hz
    exact ⟨t, ht.symm⟩
  intersections := preserve_old_cone_intersection
  common x y h := (old_common_multiple_iff x y).1 h

end PartitionConsistency.MergerAlgebra.Word

namespace PartitionConsistency.DiagramForcing.OverlapPrescription
universe u v
open DiagramOrder
variable {B : Type u} {M : Type v} [Monoid B] [Monoid M] {n : ℕ}

/-- Transport the actual overlap starts along a base homomorphism. The
pair relation remains the given one-step relation, not its transitive closure. -/
def map (P : OverlapPrescription B n) (f : B →* M) : OverlapPrescription M n where
  start i j := (P.start i j).map (fun ab => (f ab.1, f ab.2))

@[simp] theorem map_start (P : OverlapPrescription B n) (f : B →* M) (i j : Fin n) :
    (P.map f).start i j = (P.start i j).map (fun ab => (f ab.1, f ab.2)) := rfl

/-- Each prescribed identification is valid after transporting its factors. -/
theorem rel_map (P : OverlapPrescription B n) (f : B →* M)
    {i j : Fin n} {x y : B} (h : P.Rel (i,x) (j,y)) :
    (P.map f).Rel (i, f x) (j, f y) := by
  classical
  by_cases hij : i = j
  · subst j
    rw [P.rel_same_copy] at h
    exact ((P.map f).rel_same_copy i _ _).2 (congrArg f h)
  · simp only [Rel, hij, ↓reduceIte] at h ⊢
    cases he : P.start i j with
    | none => cases he ▸ h
    | some ab =>
      obtain ⟨a,b⟩ := ab
      rw [he] at h
      obtain ⟨t, rfl, rfl⟩ := h
      simp only [map_start, he, Option.map_some]
      exact ⟨f t, f.map_mul _ _, f.map_mul _ _⟩

/-- Factor conservation reflects each one-step identification, without
assuming that the prescription is valid in either monoid. -/
theorem rel_map_iff (P : OverlapPrescription B n) {f : B →* M} (hf : Conservative f)
    (i j : Fin n) (x y : B) :
    (P.map f).Rel (i, f x) (j, f y) ↔ P.Rel (i,x) (j,y) := by
  classical
  refine ⟨?_, P.rel_map f⟩
  intro h
  by_cases hij : i = j
  · subst j
    exact (P.rel_same_copy i x y).2 (hf.injective (((P.map f).rel_same_copy i _ _).1 h))
  · simp only [Rel, hij, ↓reduceIte] at h ⊢
    cases he : P.start i j with
    | none => simp only [map_start, he, Option.map_none] at h
    | some ab =>
      obtain ⟨a,b⟩ := ab
      simp only [map_start, he, Option.map_some] at h
      obtain ⟨t, hx, hy⟩ := h
      obtain ⟨u, hu⟩ := hf.factors a x t hx.symm
      exact ⟨u, hf.injective (by rw [f.map_mul, hu, ← hx]),
        hf.injective (by rw [f.map_mul, hu, ← hy])⟩

/-- Validity of a transported prescription reflects to the old monoid. -/
theorem valid_of_map (P : OverlapPrescription B n) {f : B →* M} (hf : Conservative f)
    (h : (P.map f).Valid) : P.Valid where
  refl _z := (P.rel_map_iff hf _ _ _ _).1 (h.refl _)
  symm {_z _w} hz := (P.rel_map_iff hf _ _ _ _).1 (h.symm (P.rel_map f hz))
  trans {_z _w _v} hzw hwv := (P.rel_map_iff hf _ _ _ _).1
    (h.trans (P.rel_map f hzw) (P.rel_map f hwv))

end PartitionConsistency.DiagramForcing.OverlapPrescription

namespace PartitionConsistency.DiagramForcing.OverlapPrescription
universe u v
open DiagramOrder
variable {B : Type u} {M : Type v} [Monoid B] [Monoid M] {n : ℕ}

theorem rel_start (P : OverlapPrescription B n) {i j : Fin n} (hij : i ≠ j)
    {a b : B} (ho : P.start i j = some (a,b)) : P.Rel (i,a) (j,b) := by
  simp only [Rel, hij, ↓reduceIte, ho]
  exact ⟨1, (mul_one _).symm, (mul_one _).symm⟩

theorem exists_starts_of_rel_map (P : OverlapPrescription B n) (f : B →* M)
    {i j : Fin n} (hij : i ≠ j) {x y : M} (h : (P.map f).Rel (i,x) (j,y)) :
    ∃ a b : B, P.start i j = some (a,b) ∧ ∃ t : M, x = f a * t ∧ y = f b * t := by
  simp only [Rel, hij, ↓reduceIte, map_start] at h
  cases hs : P.start i j with
  | none => simp only [hs, Option.map_none] at h
  | some ab =>
    obtain ⟨a,b⟩ := ab
    exact ⟨a,b,rfl,by simpa only [hs, Option.map_some] using h⟩

end PartitionConsistency.DiagramForcing.OverlapPrescription

namespace PartitionConsistency.DiagramForcing.OverlapPrescription
universe u v
open DiagramOrder
variable {B : Type u} {M : Type v} [LeftCancelMonoid B] [IsConical B]
  [LeftCancelMonoid M] {n : ℕ}

/-- Cone intersections, with their original right quotients, suffice to
transport a *valid* finite prescription. The transitivity check is at the
old join of the two middle-copy starts; it is not a transitive closure of
the transported prescription. Source `lem:mono-simulation`, final assertion. -/
theorem valid_map (P : OverlapPrescription B n) (hP : P.Valid)
    (hB : HasConditionalJoins (LeftDivOrder B)) {f : B →* M} (hf : Conservative f) :
    (P.map f).Valid where
  refl z := ((P.map f).rel_same_copy z.1 z.2 z.2).2 rfl
  symm := by
    rintro ⟨i,x⟩ ⟨j,y⟩ h
    by_cases hij : i = j
    · subst j
      exact ((P.map f).rel_same_copy i y x).2
        (((P.map f).rel_same_copy i x y).1 h).symm
    · obtain ⟨a,b,hs,t,rfl,rfl⟩ := P.exists_starts_of_rel_map f hij h
      exact (P.map f).rel_mul (P.rel_map f (hP.symm (P.rel_start hij hs))) t
  trans := by
    rintro ⟨i,x⟩ ⟨j,y⟩ ⟨k,z⟩ hxy hyz
    by_cases hij : i = j
    · subst j
      have h := ((P.map f).rel_same_copy i x y).1 hxy
      simpa only [h] using hyz
    by_cases hjk : j = k
    · subst k
      have h := ((P.map f).rel_same_copy j y z).1 hyz
      simpa only [h] using hxy
    obtain ⟨a,b,hs,s,hx,hy⟩ := P.exists_starts_of_rel_map f hij hxy
    obtain ⟨c,d,ht,t,hy',hz⟩ := P.exists_starts_of_rel_map f hjk hyz
    obtain ⟨q,hbq,hcq⟩ := hf.common b c ⟨y,⟨s,hy⟩,⟨t,hy'⟩⟩
    obtain ⟨j₀,hj⟩ := exists_cone_join hB b c q hbq hcq
    obtain ⟨⟨r,hr⟩,⟨u,hu⟩⟩ := (hj j₀).2 (dvd_refl j₀)
    obtain ⟨v,hv⟩ := (hf.intersections b c j₀ hj y).1 ⟨⟨s,hy⟩,⟨t,hy'⟩⟩
    have hs' : s = f r * v := mul_left_cancel (show f b * s = f b * (f r * v) by
      calc f b * s = y := hy.symm
           _ = f j₀ * v := hv
           _ = f b * (f r * v) := by rw [hr, f.map_mul, mul_assoc])
    have ht' : t = f u * v := mul_left_cancel (show f c * t = f c * (f u * v) by
      calc f c * t = y := hy'.symm
           _ = f j₀ * v := hv
           _ = f c * (f u * v) := by rw [hu, f.map_mul, mul_assoc])
    have h1 := P.rel_mul (P.rel_start hij hs) r
    have h2 := P.rel_mul (P.rel_start hjk ht) u
    have hm : b * r = c * u := hr.symm.trans hu
    rw [hm] at h1
    have h3 := (P.map f).rel_mul (P.rel_map f (hP.trans h1 h2)) v
    simpa only [hx, hz, hs', ht', f.map_mul, mul_assoc] using h3

theorem valid_map_iff (P : OverlapPrescription B n)
    (hB : HasConditionalJoins (LeftDivOrder B)) {f : B →* M} (hf : Conservative f) :
    (P.map f).Valid ↔ P.Valid := ⟨P.valid_of_map hf, fun hP => P.valid_map hP hB hf⟩

end PartitionConsistency.DiagramForcing.OverlapPrescription



namespace PartitionConsistency.DiagramOrder.Conservative
universe u v
variable {B : Type u} {M : Type v} [LeftCancelMonoid B] [IsConical B]
  [LeftCancelMonoid M] {f : B →* M} (hf : Conservative f)
include hf

/-- An upper bound in the larger monoid admits an old joint lower bound
of any two specified old divisors. -/
theorem common_below (hB : HasConditionalJoins (LeftDivOrder B))
    {x y : B} {m : M} (hx : f x ∣ m) (hy : f y ∣ m) :
    ∃ j : B, x ∣ j ∧ y ∣ j ∧ f j ∣ m := by
  obtain ⟨a,hxa,hya⟩ := hf.common x y ⟨m,hx,hy⟩
  obtain ⟨j,hj⟩ := exists_cone_join hB x y a hxa hya
  have hu := (hj j).2 (dvd_refl j)
  exact ⟨j,hu.1,hu.2,(hf.intersections x y j hj m).1 ⟨hx,hy⟩⟩

/-- Residual cones of old elements are computed using the same old join
and right quotient even when queried at a new factor. -/
theorem cone_residual (hB : HasConditionalJoins (LeftDivOrder B))
    (x a : B) {t : M} (ht : f x ∣ f a * t) :
    ∃ r : B, (∀ z : B, x ∣ a * z ↔ r ∣ z) ∧
      ∀ z : M, f x ∣ f a * z ↔ f r ∣ z := by
  obtain ⟨q,hxq,haq⟩ := hf.common x a ⟨f a * t,ht,dvd_mul_right _ _⟩
  obtain ⟨j,hj⟩ := exists_cone_join hB x a q hxq haq
  obtain ⟨r,hr⟩ := ((hj j).2 (dvd_refl j)).2
  have hnew : ∀ z : M, f x ∣ f a * z ↔ f r ∣ z := by
    intro z
    calc f x ∣ f a * z ↔ f x ∣ f a * z ∧ f a ∣ f a * z :=
          ⟨fun h => ⟨h,dvd_mul_right _ _⟩,And.left⟩
      _ ↔ f j ∣ f a * z := hf.intersections x a j hj _
      _ ↔ f r ∣ z := by rw [hr,f.map_mul,left_mul_dvd_iff]
  exact ⟨r,fun z => by simpa only [← f.map_mul, hf.dvd_iff] using hnew (f z),hnew⟩
end PartitionConsistency.DiagramOrder.Conservative

namespace PartitionConsistency.DiagramForcing.OverlapPrescription
universe u v
open DiagramOrder MergerAlgebra.RightFreeAction
variable {B : Type u} {M : Type v} [LeftCancelMonoid B] [IsConical B]
  [LeftCancelMonoid M] {n : ℕ}
variable (P : OverlapPrescription B n) (hP : P.Valid)
  (hB : HasConditionalJoins (LeftDivOrder B)) {f : B →* M} (hf : Conservative f)

/-- The genuine copy quotient embeds under conservative base simulation. -/
def copiesMap : P.Copies hP → (P.map f).Copies (P.valid_map hP hB hf) :=
  Quotient.map (fun z : Fin n × B => (z.1, f z.2))
    (fun _ _ h => P.rel_map f h)

@[simp] theorem copiesMap_copy (i : Fin n) (x : B) :
    P.copiesMap hP hB hf (P.copy hP i x) =
      (P.map f).copy (P.valid_map hP hB hf) i (f x) := rfl

theorem copiesMap_injective : Function.Injective (P.copiesMap hP hB hf) := by
  intro z w h
  obtain ⟨⟨i,x⟩,rfl⟩ := Quotient.exists_rep z
  obtain ⟨⟨j,y⟩,rfl⟩ := Quotient.exists_rep w
  exact Quotient.sound ((P.rel_map_iff hf i j x y).1 (Quotient.exact h))

@[simp] theorem copiesMap_act (z : P.Copies hP) (x : B) :
    P.copiesMap hP hB hf (act z x) = act (P.copiesMap hP hB hf z) (f x) := by
  induction z using Quotient.inductionOn with
  | h z =>
    change (P.map f).copy (P.valid_map hP hB hf) z.1 (f (z.2 * x)) =
      (P.map f).copy (P.valid_map hP hB hf) z.1 (f z.2 * f x)
    rw [f.map_mul]

/-- A right factor between smaller-copy elements stays in the old base;
validity alone would not give this assertion. -/
theorem copiesMap_factors (z w : P.Copies hP) (m : M)
    (h : act (P.copiesMap hP hB hf z) m = P.copiesMap hP hB hf w) :
    ∃ a : B, f a = m := by
  obtain ⟨⟨i,x⟩,rfl⟩ := Quotient.exists_rep z
  obtain ⟨⟨j,y⟩,rfl⟩ := Quotient.exists_rep w
  change (P.map f).copy (P.valid_map hP hB hf) i (f x * m) =
    (P.map f).copy (P.valid_map hP hB hf) j (f y) at h
  have hr := ((P.map f).copy_eq_iff (P.valid_map hP hB hf) i j _ _).1 h
  by_cases hij : i = j
  · subst j
    exact hf.factors x y m (((P.map f).rel_same_copy i _ _).1 hr)
  · obtain ⟨a,b,_,t,hx,hy⟩ := P.exists_starts_of_rel_map f hij hr
    obtain ⟨s,hs⟩ := hf.factors b y t hy.symm
    have hm : f x * m = f (a * s) := by rw [f.map_mul,hs,hx]
    exact hf.factors x (a * s) m hm

/-- The finite-overlap cone calculation lifts an old common lower bound
below each larger common upper bound. This proves preservation both of
all old joins and of nonjoins, not just injectivity of the quotient map. -/
theorem copiesMap_common_below (z w : P.Copies hP)
    (c : (P.map f).Copies (P.valid_map hP hB hf))
    (hz : Reaches M (P.copiesMap hP hB hf z) c)
    (hw : Reaches M (P.copiesMap hP hB hf w) c) :
    ∃ j : P.Copies hP, Reaches B z j ∧ Reaches B w j ∧
      Reaches M (P.copiesMap hP hB hf j) c := by
  obtain ⟨⟨i,x⟩,rfl⟩ := Quotient.exists_rep z
  obtain ⟨⟨j,y⟩,rfl⟩ := Quotient.exists_rep w
  obtain ⟨u,hu⟩ := hz
  obtain ⟨v,hv⟩ := hw
  change (P.map f).copy (P.valid_map hP hB hf) i (f x * u) = c at hu
  change (P.map f).copy (P.valid_map hP hB hf) j (f y * v) = c at hv
  by_cases hij : i = j
  · subst j
    have hxy : f x * u = f y * v :=
      (P.map f).copy_injective (P.valid_map hP hB hf) i (hu.trans hv.symm)
    obtain ⟨k,hxk,hyk,t,ht⟩ := hf.common_below hB (dvd_mul_right (f x) u) ⟨v,hxy⟩
    refine ⟨P.copy hP i k,(P.reaches_same_copy_iff hP i x k).2 hxk,
      (P.reaches_same_copy_iff hP i y k).2 hyk,t,?_⟩
    change (P.map f).copy (P.valid_map hP hB hf) i (f k * t) = c
    rw [← ht,hu]
  · have hr := ((P.map f).copy_eq_iff (P.valid_map hP hB hf) i j _ _).1 (hu.trans hv.symm)
    obtain ⟨a,b,hs,t,hxt,hyt⟩ := P.exists_starts_of_rel_map f hij hr
    have hx : f x ∣ f a * t := ⟨u,hxt.symm⟩
    have hy : f y ∣ f b * t := ⟨v,hyt.symm⟩
    obtain ⟨r,hr,hr'⟩ := hf.cone_residual hB x a hx
    obtain ⟨s,hs₀,hs'⟩ := hf.cone_residual hB y b hy
    obtain ⟨k,hrk,hsk,d,hd⟩ := hf.common_below hB ((hr' t).1 hx) ((hs' t).1 hy)
    have hrel : P.copy hP i (a * k) = P.copy hP j (b * k) :=
      (P.copy_eq_iff hP i j _ _).2 (P.rel_mul (P.rel_start hij hs) k)
    refine ⟨P.copy hP i (a * k),(P.reaches_same_copy_iff hP i x _).2 ((hr k).2 hrk),
      ?_,d,?_⟩
    · rw [hrel]
      exact (P.reaches_same_copy_iff hP j y _).2 ((hs₀ k).2 hsk)
    · change (P.map f).copy (P.valid_map hP hB hf) i (f (a * k) * d) = c
      rw [f.map_mul,mul_assoc,← hd,← hxt,hu]

end PartitionConsistency.DiagramForcing.OverlapPrescription

namespace PartitionConsistency.MergerAlgebra.Word
universe u v w z
open DiagramOrder RightFreeAction
variable {B : Type u} {M : Type v} {D : Type w} {E : Type z}
  [Monoid B] [Monoid M]

/-- Simulation on literal merger normal forms, by transporting each
coefficient and each final-letter quotient class. -/
def transport (f : B →* M) (g : D → E) : Word B D → Word M E
  | old x => old (f x)
  | snoc t d => snoc (transport f g t) (g d)

@[simp] theorem transport_old (f : B →* M) (g : D → E) (x : B) :
    transport f g (old x) = old (f x) := rfl
@[simp] theorem transport_snoc (f : B →* M) (g : D → E) (t : Word B D) (d : D) :
    transport f g (snoc t d) = snoc (transport f g t) (g d) := rfl

variable [RightFreeAction B D] [RightFreeAction M E]
  (f : B →* M) (g : D → E)
  (hgact : ∀ d x, g (RightFreeAction.act d x) = RightFreeAction.act (g d) (f x))

include hgact in
@[simp] theorem transport_act (x : Word B D) (a : B) :
    transport f g (act x a) = act (transport f g x) (f a) := by
  cases x with
  | old x => exact congrArg old (f.map_mul x a)
  | snoc x d => exact congrArg (snoc (transport f g x)) (hgact d a)

include hgact in
@[simp] theorem transport_mul (x y : Word B D) :
    transport f g (x * y) = transport f g x * transport f g y := by
  induction y with
  | old a => exact transport_act f g hgact x a
  | snoc y d ih => exact congrArg (snoc · (g d)) ih

def transportHom : Word B D →* Word M E where
  toFun := transport f g
  map_one' := congrArg old f.map_one
  map_mul' := transport_mul f g hgact

@[simp] theorem transportHom_apply (x : Word B D) :
    transportHom f g hgact x = transport f g x := rfl

omit [RightFreeAction B D] [RightFreeAction M E] in
theorem transport_injective (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (transport f g) := by
  intro x
  induction x with
  | old x =>
    intro y he
    cases y with
    | old y => exact congrArg old (hf (Word.old.inj he))
    | snoc y d => cases he
  | snoc x d ih =>
    intro y he
    cases y with
    | old y => cases he
    | snoc y e =>
      obtain ⟨hxy,hde⟩ := Word.snoc.inj he
      exact congrArg₂ snoc (ih hxy) (hg hde)

omit [RightFreeAction B D] in
/-- Right division of two simulated normal forms produces a smaller
normal form. This is stronger than existence of some reflected divisor. -/
theorem transport_factors (hf : Conservative f)
    (hgf : ∀ d e : D, ∀ a : M, RightFreeAction.act (g d) a = g e → ∃ b : B, f b = a)
    (x y : Word B D) (q : Word M E)
    (h : transport f g x * q = transport f g y) :
    ∃ r : Word B D, transport f g r = q := by
  induction y generalizing x q with
  | old y =>
    obtain ⟨a,m,hx,rfl,ham⟩ := factors_of_old h
    cases x with
    | old x =>
      have ha := Word.old.inj hx
      obtain ⟨b,hb⟩ := hf.factors x y m (ha ▸ ham)
      exact ⟨old b,congrArg old hb⟩
    | snoc x d => cases hx
  | snoc y d ih =>
    cases q with
    | old m =>
      cases x with
      | old x => cases h
      | snoc x e =>
        obtain ⟨_,hm⟩ := Word.snoc.inj h
        obtain ⟨b,hb⟩ := hgf e d m hm
        exact ⟨old b,congrArg old hb⟩
    | snoc q e =>
      obtain ⟨hp,he⟩ := Word.snoc.inj h
      obtain ⟨r,hr⟩ := ih x q hp
      exact ⟨snoc r d,congrArg₂ snoc hr he.symm⟩

include hgact in
theorem transport_dvd_iff (hf : Conservative f) (hg : Function.Injective g)
    (hgf : ∀ d e : D, ∀ a : M, RightFreeAction.act (g d) a = g e → ∃ b : B, f b = a)
    (x y : Word B D) : transport f g x ∣ transport f g y ↔ x ∣ y := by
  constructor
  · rintro ⟨q,hq⟩
    obtain ⟨r,hr⟩ := transport_factors f g hf hgf x y q hq.symm
    refine ⟨r,transport_injective f g hf.injective hg ?_⟩
    rw [transport_mul f g hgact,hr,hq]
  · exact (transportHom f g hgact).map_dvd

end PartitionConsistency.MergerAlgebra.Word

namespace PartitionConsistency.MergerAlgebra.Word
universe u v w z
open DiagramOrder RightFreeAction
variable {B : Type u} {M : Type v} {D : Type w} {E : Type z}
  [LeftCancelMonoid B] [IsConical B] [LeftCancelMonoid M]
  [RightFreeAction B D] [RightFreeAction M E]
variable (hB : HasConditionalJoins (LeftDivOrder B))
  (f : B →* M) (g : D → E)
  (hgact : ∀ d x, g (RightFreeAction.act d x) = RightFreeAction.act (g d) (f x))
  (hf : Conservative f) (hg : Function.Injective g)
  (hgf : ∀ d e : D, ∀ a : M, RightFreeAction.act (g d) a = g e → ∃ b : B, f b = a)
  (hgc : ∀ d e : D, ∀ c : E, Reaches M (g d) c → Reaches M (g e) c →
    ∃ j : D, Reaches B d j ∧ Reaches B e j ∧ Reaches M (g j) c)

include hB hgact hf hg hgf hgc

/-- Joint lower bounds of old divisors are lifted by induction on the
literal larger upper bound. At unequal lengths the comparison reflects
by right-factor conservation; at equal lengths the final-letter cone
calculation controls the intersection. -/
theorem transport_common_below (x y : Word B D) (c : Word M E)
    (hx : transport f g x ∣ c) (hy : transport f g y ∣ c) :
    ∃ j : Word B D, x ∣ j ∧ y ∣ j ∧ transport f g j ∣ c := by
  induction c generalizing x y with
  | old m =>
    cases x with
    | snoc x d => exact (snoc_not_dvd_old _ _ _ hx).elim
    | old x =>
      cases y with
      | snoc y d => exact (snoc_not_dvd_old _ _ _ hy).elim
      | old y =>
        obtain ⟨j,hxj,hyj,hjm⟩ := hf.common_below hB
          ((old_dvd_iff (f x) (old m)).1 hx) ((old_dvd_iff (f y) (old m)).1 hy)
        exact ⟨old j,(oldHom : B →* Word B D).map_dvd hxj,
          (oldHom : B →* Word B D).map_dvd hyj,(old_dvd_iff (f j) (old m)).2 hjm⟩
  | snoc c d ih =>
    rcases (dvd_snoc_iff (transport f g x) c d).1 hx with hxc | ⟨dx,hxe,hxd⟩
    · rcases (dvd_snoc_iff (transport f g y) c d).1 hy with hyc | ⟨dy,hye,_⟩
      · obtain ⟨j,hxj,hyj,hjc⟩ := ih x y hxc hyc
        exact ⟨j,hxj,hyj,(dvd_snoc_iff _ _ _).2 (Or.inl hjc)⟩
      · have hxy : transport f g x ∣ transport f g y := by
          rw [hye]
          exact (dvd_snoc_iff _ _ _).2 (Or.inl hxc)
        exact ⟨y,(transport_dvd_iff f g hgact hf hg hgf x y).1 hxy,dvd_refl y,hy⟩
    · rcases (dvd_snoc_iff (transport f g y) c d).1 hy with hyc | ⟨dy,hye,hyd⟩
      · have hyx : transport f g y ∣ transport f g x := by
          rw [hxe]
          exact (dvd_snoc_iff _ _ _).2 (Or.inl hyc)
        exact ⟨x,dvd_refl x,(transport_dvd_iff f g hgact hf hg hgf y x).1 hyx,hx⟩
      · cases x with
        | old x => cases hxe
        | snoc x a =>
          cases y with
          | old y => cases hye
          | snoc y b =>
            obtain ⟨hxc,hax⟩ := Word.snoc.inj hxe
            obtain ⟨hyc,hby⟩ := Word.snoc.inj hye
            have hxy := transport_injective f g hf.injective hg (hxc.trans hyc.symm)
            subst y
            obtain ⟨j,haj,hbj,hjd⟩ := hgc a b d (hax ▸ hxd) (hby ▸ hyd)
            refine ⟨snoc x j,(snoc_dvd_snoc_iff _ _ _ _).2 (Or.inr ⟨rfl,haj⟩),
              (snoc_dvd_snoc_iff _ _ _ _).2 (Or.inr ⟨rfl,hbj⟩),?_⟩
            change snoc (transport f g x) (g j) ∣ snoc c d
            rw [hxc]
            exact (snoc_dvd_snoc_iff _ _ _ _).2 (Or.inr ⟨rfl,hjd⟩)

/-- The entire merger normal-form simulation is conservative. -/
theorem transport_conservative : Conservative (transportHom f g hgact) where
  injective := transport_injective f g hf.injective hg
  factors := transport_factors f g hf hgf
  intersections x y j hj c := by
    constructor
    · rintro ⟨hx,hy⟩
      obtain ⟨k,hxk,hyk,hkc⟩ := transport_common_below hB f g hgact hf hg hgf hgc x y c hx hy
      exact ((transportHom f g hgact).map_dvd ((hj k).1 ⟨hxk,hyk⟩)).trans hkc
    · intro h
      have hu := (hj j).2 (dvd_refl j)
      exact ⟨((transportHom f g hgact).map_dvd hu.1).trans h,
        ((transportHom f g hgact).map_dvd hu.2).trans h⟩
  common x y h := by
    obtain ⟨c,hx,hy⟩ := h
    obtain ⟨j,hxj,hyj,_⟩ := transport_common_below hB f g hgact hf hg hgf hgc x y c hx hy
    exact ⟨j,hxj,hyj⟩

end PartitionConsistency.MergerAlgebra.Word

namespace PartitionConsistency.DiagramForcing.OverlapPrescription
universe u v
open DiagramOrder MergerAlgebra
variable {B : Type u} {M : Type v} [LeftCancelMonoid B] [IsConical B]
  [LeftCancelMonoid M] {n : ℕ}
variable (P : OverlapPrescription B n) (hP : P.Valid)
  (hB : HasConditionalJoins (LeftDivOrder B)) {f : B →* M} (hf : Conservative f)

/-- Simulate exactly the smaller merger presentation in the larger base,
using the same prescribed overlap starts. -/
def mergerSimulation : Word B (P.Copies hP) →*
    Word M ((P.map f).Copies (P.valid_map hP hB hf)) :=
  Word.transportHom f (P.copiesMap hP hB hf) (P.copiesMap_act hP hB hf)

/-- Merger case of source `lem:mono-simulation`: the induced homomorphism
is conservative, including old factors, all cone intersections, and nonjoins. -/
theorem mergerSimulation_conservative : Conservative (P.mergerSimulation hP hB hf) :=
  Word.transport_conservative hB f (P.copiesMap hP hB hf) (P.copiesMap_act hP hB hf)
    hf (P.copiesMap_injective hP hB hf) (P.copiesMap_factors hP hB hf)
    (P.copiesMap_common_below hP hB hf)

@[simp] theorem mergerSimulation_old (x : B) :
    P.mergerSimulation hP hB hf (Word.old x) = Word.old (f x) := rfl

@[simp] theorem mergerSimulation_snoc (x : Word B (P.Copies hP)) (i : Fin n) (a : B) :
    P.mergerSimulation hP hB hf (Word.snoc x (P.copy hP i a)) =
      Word.snoc (P.mergerSimulation hP hB hf x)
        ((P.map f).copy (P.valid_map hP hB hf) i (f a)) := rfl

end PartitionConsistency.DiagramForcing.OverlapPrescription

end OAI
