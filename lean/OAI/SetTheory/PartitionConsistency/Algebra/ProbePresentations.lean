import Mathlib
import OAI.SetTheory.PartitionConsistency.Algebra.ConservativeExtensions

namespace OAI

namespace PartitionConsistency.ProbeAlgebra.Path
universe u v
open DiagramOrder
variable {B : Type u} {M : Type v} [LeftCancelMonoid B] [LeftCancelMonoid M]
  {a : B} (P : Path B a) (f : B →* M)

/-- The same countable probe presentation over the larger base. -/
def map : Path M (f a) where
  node i := f (P.node i)
  zero := by rw [P.zero, f.map_one]
  increasing h := f.map_dvd (P.increasing h)
  bounded i := f.map_dvd (P.bounded i)

@[simp] theorem map_node (i : ℕ) : (P.map f).node i = f (P.node i) := rfl

@[simp] theorem map_factor (i j : ℕ) (h : i ≤ j) :
    (P.map f).factor i j h = f (P.factor i j h) := by
  apply mul_left_cancel (a := f (P.node i))
  calc
    f (P.node i) * (P.map f).factor i j h = f (P.node j) := (P.map f).node_factor i j h
    _ = f (P.node i * P.factor i j h) := congrArg f (P.node_factor i j h).symm
    _ = f (P.node i) * f (P.factor i j h) := f.map_mul _ _

@[simp] theorem map_terminal (i : ℕ) :
    (P.map f).terminal i = f (P.terminal i) := by
  apply mul_left_cancel (a := f (P.node i))
  calc
    f (P.node i) * (P.map f).terminal i = f a := (P.map f).node_terminal i
    _ = f (P.node i * P.terminal i) := congrArg f (P.node_terminal i).symm
    _ = f (P.node i) * f (P.terminal i) := f.map_mul _ _

/-- Map the actual, potentially non-injective direct limits. -/
noncomputable def lettersMap : P.Letters → (P.map f).Letters :=
  DirectLimit.map P.transition (P.map f).transition (fun _ => f)
    (fun i j hij x => by simp only [transition_apply, map_factor, f.map_mul])

@[simp] theorem lettersMap_letter (i : ℕ) (x : B) :
    P.lettersMap f (P.letter i x) = (P.map f).letter i (f x) := rfl

include P in
/-- Reflection is tested at a common finite stage, not by cancellation
of the (possibly non-injective) transition maps. -/
theorem lettersMap_injective (hf : Function.Injective f) :
    Function.Injective (P.lettersMap f) := by
  intro s t he
  obtain ⟨i,x,rfl⟩ := DirectLimit.exists_eq_mk P.transition s
  obtain ⟨j,y,rfl⟩ := DirectLimit.exists_eq_mk P.transition t
  obtain ⟨k,hi,hj,hk⟩ := ((P.map f).letter_eq_iff i j (f x) (f y)).1 he
  apply (P.letter_eq_iff i j x y).2
  refine ⟨k,hi,hj,hf ?_⟩
  simpa only [map_factor, ← f.map_mul] using hk

@[simp] theorem lettersMap_act (x : B) (s : P.Letters) :
    P.lettersMap f (P.act x s) = (P.map f).act (f x) (P.lettersMap f s) := by
  induction s using DirectLimit.induction with
  | ih i y =>
    change (P.map f).letter i (f (x * y)) = (P.map f).letter i (f x * f y)
    rw [f.map_mul]

@[simp] theorem lettersMap_exit (e : B) (s : P.Letters) :
    (P.map f).exit (f e) (P.lettersMap f s) = f (P.exit e s) := by
  induction s using DirectLimit.induction with
  | ih i y =>
    change (P.map f).exit (f e) (P.lettersMap f (P.letter i y)) = f (P.exit e (P.letter i y))
    simp only [lettersMap_letter, exit, target_letter, map_terminal, f.map_mul]

/-- Smaller-letter divisibility is reflected with its exact quotient:
a larger-stage witness can be pulled back by old-factor conservation. -/
theorem lettersMap_inCone_iff (hf : Conservative f) (x : B) (s : P.Letters) :
    (P.map f).InCone (f x) (P.lettersMap f s) ↔ P.InCone x s := by
  induction s using DirectLimit.induction with
  | ih i y =>
    change (P.map f).InCone (f x) ((P.map f).letter i (f y)) ↔ P.InCone x (P.letter i y)
    simp only [inCone_letter_iff, map_factor, ← f.map_mul, hf.dvd_iff]

end PartitionConsistency.ProbeAlgebra.Path

namespace PartitionConsistency.ProbeAlgebra
universe u v w z
open DiagramOrder

/-- A map of probe alphabets whose old divisibility tests are unchanged.
All these laws will be proved for the path direct limits; no assumptions
about joins between new words or their gates enter this definition. -/
structure AlphabetSimulation {B : Type u} {M : Type v} {S : Type w} {T : Type z}
    [LeftCancelMonoid B] [LeftCancelMonoid M]
    (A : Alphabet B S) (C : Alphabet M T) (f : B →* M) (g : S → T) : Prop where
  injective : Function.Injective g
  act : ∀ x s, g (A.act x s) = C.act (f x) (g s)
  exit : ∀ s, C.exit (g s) = f (A.exit s)
  cones : ∀ x s, (∃ t : T, C.act (f x) t = g s) ↔ ∃ t : S, A.act x t = s

namespace Path
variable {B : Type u} {M : Type v} [LeftCancelMonoid B] [IsConical B]
  [LeftCancelMonoid M] [IsConical M] {a e : B} (P : Path B a) (he : e ≠ 1)
  {f : B →* M} (hf : Conservative f)

/-- A conservative map of bases supplies an alphabet simulation for the
same generators and terminal parameter. -/
theorem alphabetSimulation : AlphabetSimulation (P.alphabet he)
    ((P.map f).alphabet (fun h => he (hf.injective (h.trans f.map_one.symm)))) f
    (P.lettersMap f) where
  injective := P.lettersMap_injective f hf.injective
  act := P.lettersMap_act f
  exit := P.lettersMap_exit f e
  cones := P.lettersMap_inCone_iff f hf

end Path

namespace Raw
variable {B : Type u} {M : Type v} {S : Type w} {T : Type z}

/-- Simulation on literal strings. Reducedness will be proved, not
postulated or hidden in a quotient of these words. -/
def transport (f : B → M) (g : S → T) : Raw B S → Raw M T
  | old x => old (f x)
  | cons s w => cons (g s) (transport f g w)

@[simp] theorem transport_old (f : B → M) (g : S → T) (x : B) :
    transport f g (old x) = old (f x) := rfl
@[simp] theorem transport_cons (f : B → M) (g : S → T) (s : S) (x : Raw B S) :
    transport f g (cons s x) = cons (g s) (transport f g x) := rfl

theorem transport_injective {f : B → M} {g : S → T}
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (transport f g) := by
  intro x
  induction x with
  | old x =>
    intro y he
    cases y with
    | old y => exact congrArg old (hf (Raw.old.inj he))
    | cons s y => cases he
  | cons s x ih =>
    intro y he
    cases y with
    | old y => cases he
    | cons t y =>
      obtain ⟨hst,hxy⟩ := Raw.cons.inj he
      exact congrArg₂ cons (hg hst) (ih hxy)

variable [LeftCancelMonoid B] [LeftCancelMonoid M]
  {A : Alphabet B S} {C : Alphabet M T} {f : B →* M} {g : S → T}
  (hf : Conservative f) (hg : AlphabetSimulation A C f g)

include hf hg in
@[simp] theorem headDiv_transport (x : B) (y : Raw B S) :
    (transport f g y).headDiv C (f x) ↔ y.headDiv A x := by
  cases y with
  | old y => exact hf.dvd_iff x y
  | cons s y => exact hg.cones x s

include hf hg in
@[simp] theorem reduced_transport (b : B) (y : Raw B S) :
    (transport f g y).reduced C (f b) ↔ y.reduced A b := by
  induction y with
  | old y => rfl
  | cons s y ih =>
    change ((transport f g y).reduced C (f b) ∧ ¬ (transport f g y).headDiv C (f b)) ↔ _
    rw [ih,headDiv_transport hf hg]
    rfl

include hg in
@[simp] theorem transport_oldAct (x : B) (y : Raw B S) :
    transport f g (oldAct A x y) = oldAct C (f x) (transport f g y) := by
  cases y with
  | old y => exact congrArg old (f.map_mul x y)
  | cons s y => exact congrArg (cons · (transport f g y)) (hg.act x s)

end Raw

namespace Word
variable {B : Type u} {M : Type v} {S : Type w} {T : Type z}
  [LeftCancelMonoid B] [LeftCancelMonoid M]
  {A : Alphabet B S} {C : Alphabet M T} {f : B →* M} {g : S → T}
  (hf : Conservative f) (hg : AlphabetSimulation A C f g) (b : B)

/-- Smaller irreducible words remain irreducible in the larger presentation. -/
def transport (y : Word A b) : Word C (f b) :=
  ⟨Raw.transport f g y.val, (Raw.reduced_transport hf hg b y.val).2 y.property⟩

@[simp] theorem transport_old (x : B) :
    transport hf hg b (old A b x) = old C (f b) (f x) := rfl

@[simp] theorem transport_cons (s : S) (y : Word A b) (hy) :
    transport hf hg b (cons A b s y hy) =
      cons C (f b) (g s) (transport hf hg b y)
        (fun h => hy ((Raw.headDiv_transport hf hg b y.val).1 h)) := rfl

@[simp] theorem head_transport (y : Word A b) :
    head C (f b) (transport hf hg b y) = (head A b y).map g := by
  obtain ⟨y,hy⟩ := y
  cases y <;> rfl

@[simp] theorem headDiv_transport (x : B) (y : Word A b) :
    headDiv C (f b) (f x) (transport hf hg b y) ↔ headDiv A b x y :=
  Raw.headDiv_transport hf hg x y.val

theorem transport_injective : Function.Injective (transport hf hg b) :=
  fun _ _ h => Subtype.ext (Raw.transport_injective hf.injective hg.injective
    (congrArg Subtype.val h))

@[simp] theorem transport_oldAct (x : B) (y : Word A b) :
    transport hf hg b (oldAct A b x y) = oldAct C (f b) (f x) (transport hf hg b y) :=
  Subtype.ext (Raw.transport_oldAct hg x y.val)

@[simp] theorem transport_quotient (x : B) (y : Word A b) (hy) :
    transport hf hg b (quotient A b x y hy) =
      quotient C (f b) (f x) (transport hf hg b y)
        ((headDiv_transport hf hg b x y).2 hy) := by
  apply oldAct_injective C (f b) (f x)
  rw [← transport_oldAct, oldAct_quotient, oldAct_quotient]

@[simp] theorem transport_letterAct (s : S) (y : Word A b) :
    transport hf hg b (letterAct A b s y) =
      letterAct C (f b) (g s) (transport hf hg b y) := by
  classical
  by_cases hy : headDiv A b b y
  · rw [letterAct_of_headDiv A b s y hy,
      letterAct_of_headDiv C (f b) (g s) _ ((headDiv_transport hf hg b b y).2 hy),
      transport_oldAct,transport_quotient,hg.exit]
  · rw [letterAct_of_not_headDiv A b s y hy,
      letterAct_of_not_headDiv C (f b) (g s) _
        (fun h => hy ((headDiv_transport hf hg b b y).1 h)),transport_cons]

@[simp] theorem transport_mul (x y : Word A b) :
    transport hf hg b (x * y) = transport hf hg b x * transport hf hg b y := by
  obtain ⟨x,hx⟩ := x
  induction x with
  | old x => exact transport_oldAct hf hg b x y
  | cons s x ih =>
    change x.reduced A b ∧ ¬ x.headDiv A b at hx
    change transport hf hg b (letterAct A b s (⟨x,hx.1⟩ * y)) =
      letterAct C (f b) (g s) (transport hf hg b ⟨x,hx.1⟩ * transport hf hg b y)
    rw [transport_letterAct,ih hx.1]

/-- The literal normal-form embedding respects the defining reductions. -/
def transportHom : Word A b →* Word C (f b) where
  toFun := transport hf hg b
  map_one' := congrArg (old C (f b)) f.map_one
  map_mul' := transport_mul hf hg b

@[simp] theorem transportHom_apply (x : Word A b) :
    transportHom hf hg b x = transport hf hg b x := rfl

theorem old_dvd_transport_iff (x : B) (y : Word A b) :
    old C (f b) (f x) ∣ transport hf hg b y ↔ old A b x ∣ y := by
  rw [old_dvd_iff_headDiv,headDiv_transport,old_dvd_iff_headDiv]

end Word
end PartitionConsistency.ProbeAlgebra

namespace PartitionConsistency.ProbeAlgebra.Word
universe u v w z
open DiagramOrder
variable {B : Type u} {M : Type v} {S : Type w} {T : Type z}
  [LeftCancelMonoid B] [IsConical B] [LeftCancelMonoid M]
  {A : Alphabet B S} {C : Alphabet M T} {f : B →* M} {g : S → T}
  (hf : Conservative f) (hg : AlphabetSimulation A C f g) (b : B)
  (hB : HasConditionalJoins (LeftDivOrder B))
  (hA : Conservative (oldHom A b)) (hC : Conservative (oldHom C (f b)))

include hf hB hA hC in
/-- The old intersection used in the gate recursion is the same on both
sides, including its original right quotients. -/
theorem simulated_old_intersection (x y : B) (q : Word C (f b))
    (hx : old C (f b) (f x) ∣ q) (hy : old C (f b) (f y) ∣ q) :
    ∃ j : B, (∀ v : Word A b, old A b x ∣ v ∧ old A b y ∣ v ↔ old A b j ∣ v) ∧
      ∀ v : Word C (f b), old C (f b) (f x) ∣ v ∧ old C (f b) (f y) ∣ v ↔
        old C (f b) (f j) ∣ v := by
  obtain ⟨m,hxm,hym⟩ := (hf.comp hC).common x y ⟨q,hx,hy⟩
  obtain ⟨j,hj⟩ := exists_cone_join hB x y m hxm hym
  exact ⟨j,hA.intersections x y j hj,(hf.comp hC).intersections x y j hj⟩

include hB hA hC in
/-- An exit in the larger presentation determines exactly the same old
gate in both presentations. Induction computes gates using the transported
old joins; the existence/nonexistence of a gate is not an assumption. -/
theorem exists_simulated_gate_of_exit (x : Word A b) {s : S}
    (hx : head A b x = some s) {q : Word C (f b)}
    (hxq : transport hf hg b x ∣ q) (hq : head C (f b) q ≠ some (g s)) :
    ∃ j : B, Gate A b x s j ∧ Gate C (f b) (transport hf hg b x) (g s) (f j) := by
  obtain ⟨x,hxred⟩ := x
  induction x generalizing s q with
  | old x => cases hx
  | cons t Y ih =>
    have hts : t = s := Option.some.inj hx
    subst t
    change Y.reduced A b ∧ ¬ Y.headDiv A b at hxred
    let Y' : Word A b := ⟨Y,hxred.1⟩
    obtain ⟨v,hv⟩ := hxq
    have hbyv : old C (f b) (f b) ∣ transport hf hg b Y' * v := by
      apply (old_dvd_iff_headDiv C (f b) (f b) _).2
      apply (head_letterAct_ne_iff C (f b) (g s) _).1
      exact (congrArg (head C (f b)) hv) ▸ hq
    have hInt : ∃ j : B,
        (∀ w : Word A b, Y' ∣ w ∧ old A b b ∣ w ↔ old A b j ∣ w) ∧
        ∀ w : Word C (f b), transport hf hg b Y' ∣ w ∧ old C (f b) (f b) ∣ w ↔
          old C (f b) (f j) ∣ w := by
      cases heY : Y with
      | old y =>
        have hYeq : Y' = old A b y := Subtype.ext heY
        rw [hYeq] at ⊢ hbyv
        exact simulated_old_intersection hf b hB hA hC y b
          (transport hf hg b (old A b y) * v) (dvd_mul_right _ _) hbyv
      | cons t Z =>
        have hYhead : head A b Y' = some t := by change Y.head = some t; rw [heY]; rfl
        have hThead : head C (f b) (transport hf hg b Y') = some (g t) := by
          rw [head_transport,hYhead]; rfl
        have hbnY : ¬ headDiv C (f b) (f b) (transport hf hg b Y') :=
          fun h => hxred.2 ((headDiv_transport hf hg b b Y').1 h)
        have hex : head C (f b) (transport hf hg b Y' * v) ≠ some (g t) := by
          intro hh
          exact hbnY ((headDiv_of_same_head C (f b) hThead hh).2
            ((old_dvd_iff_headDiv C (f b) (f b) _).1 hbyv))
        obtain ⟨k,hk,hk'⟩ := ih hex hxred.1 hYhead (dvd_mul_right _ _)
        obtain ⟨j,hj,hj'⟩ := simulated_old_intersection hf b hB hA hC k b
          (transport hf hg b Y' * v) ((hk' _).1 ⟨dvd_mul_right _ _,hex⟩) hbyv
        refine ⟨j,fun w => ?_,fun w => ?_⟩
        · calc
            Y' ∣ w ∧ old A b b ∣ w ↔ old A b b ∣ w ∧ Y' ∣ w := and_comm
            _ ↔ old A b b ∣ w ∧ old A b k ∣ w := Gate.old_intersection A b hk hYhead hxred.2 w
            _ ↔ old A b k ∣ w ∧ old A b b ∣ w := and_comm
            _ ↔ old A b j ∣ w := hj w
        · calc
            transport hf hg b Y' ∣ w ∧ old C (f b) (f b) ∣ w ↔
                old C (f b) (f b) ∣ w ∧ transport hf hg b Y' ∣ w := and_comm
            _ ↔ old C (f b) (f b) ∣ w ∧ old C (f b) (f k) ∣ w :=
                Gate.old_intersection C (f b) hk' hThead hbnY w
            _ ↔ old C (f b) (f k) ∣ w ∧ old C (f b) (f b) ∣ w := and_comm
            _ ↔ old C (f b) (f j) ∣ w := hj' w
    obtain ⟨j,hj,hj'⟩ := hInt
    have hbj : b ∣ j :=
      (old_dvd_old_iff A b b j).1 (((hj _).2 (dvd_refl _)).2)
    obtain ⟨u,rfl⟩ := hbj
    refine ⟨A.exit s * u,gate_of_suffix_intersection A b s Y' hxred.2 u hj,?_⟩
    have hY' : ¬ headDiv C (f b) (f b) (transport hf hg b Y') :=
      fun h => hxred.2 ((headDiv_transport hf hg b b Y').1 h)
    have h := gate_of_suffix_intersection C (f b) (g s) (transport hf hg b Y') hY' (f u)
      (fun w => by simpa only [f.map_mul] using hj' w)
    change Gate C (f b) (cons C (f b) (g s) (transport hf hg b Y') hY') (g s)
      (f (A.exit s * u))
    simpa only [hg.exit,f.map_mul] using h

end PartitionConsistency.ProbeAlgebra.Word

namespace PartitionConsistency.ProbeAlgebra.Word
universe u v w z
open DiagramOrder
variable {B : Type u} {M : Type v} {S : Type w} {T : Type z}
  [LeftCancelMonoid B] [IsConical B] [LeftCancelMonoid M]
  {A : Alphabet B S} {C : Alphabet M T} {f : B →* M} {g : S → T}
  (hf : Conservative f) (hg : AlphabetSimulation A C f g) (b : B)

omit [IsConical B] in
@[simp] theorem head_transport_eq_some (x : Word A b) (s : S) :
    head C (f b) (transport hf hg b x) = some (g s) ↔ head A b x = some s := by
  rw [head_transport]
  cases he : head A b x with
  | none => simp
  | some t => simp only [Option.map_some, Option.some.injEq, hg.injective.eq_iff]

omit [IsConical B] in
/-- Once a comparison reflects, cancellation reflects its particular
factor, not just the existence of some factor. -/
theorem transport_factor_of_dvd (x y : Word A b) (q : Word C (f b))
    (h : transport hf hg b x * q = transport hf hg b y) (hxy : x ∣ y) :
    ∃ r : Word A b, transport hf hg b r = q := by
  obtain ⟨r,hr⟩ := hxy
  refine ⟨r,mul_left_cancel (a := transport hf hg b x) ?_⟩
  calc
    transport hf hg b x * transport hf hg b r = transport hf hg b (x * r) :=
      (transport_mul hf hg b x r).symm
    _ = transport hf hg b y := congrArg (transport hf hg b) hr.symm
    _ = transport hf hg b x * q := h.symm

variable (hB : HasConditionalJoins (LeftDivOrder B))
  (hA : Conservative (oldHom A b)) (hC : Conservative (oldHom C (f b)))

include hB hA hC in
/-- Source `lem:mono-simulation`, separate division argument for probes.
Old heads use letter-cone reflection; equal new heads cancel; an exit
factors through the shared old gate furnished by the gate recursion. -/
theorem transport_factors (x y : Word A b) (q : Word C (f b))
    (h : transport hf hg b x * q = transport hf hg b y) :
    ∃ r : Word A b, transport hf hg b r = q := by
  obtain ⟨x,hx⟩ := x
  induction x generalizing y q with
  | old x =>
    exact transport_factor_of_dvd hf hg b (old A b x) y q h
      ((old_dvd_transport_iff hf hg b x y).1 ⟨q,h.symm⟩)
  | cons s Y ih =>
    change Y.reduced A b ∧ ¬ Y.headDiv A b at hx
    let Y' : Word A b := ⟨Y,hx.1⟩
    change transport hf hg b (cons A b s Y' hx.2) * q = transport hf hg b y at h
    by_cases hys : head C (f b) (transport hf hg b y) = some (g s)
    · obtain ⟨Z,hZ,rfl⟩ := (head_eq_some_iff A b y s).1
        ((head_transport_eq_some hf hg b y s).1 hys)
      have hZ' : ¬ headDiv C (f b) (f b) (transport hf hg b Z) :=
        fun hh => hZ ((headDiv_transport hf hg b b Z).1 hh)
      have he : transport hf hg b Y' * q = transport hf hg b Z := by
        apply letterAct_injective C (f b) (g s)
        calc
          letterAct C (f b) (g s) (transport hf hg b Y' * q) =
              transport hf hg b (cons A b s Z hZ) := h
          _ = letterAct C (f b) (g s) (transport hf hg b Z) :=
            (letterAct_of_not_headDiv C (f b) (g s) _ hZ').symm
      exact ih Z q hx.1 he
    · obtain ⟨j,hj,hj'⟩ := exists_simulated_gate_of_exit hf hg b hB hA hC
        (cons A b s Y' hx.2) rfl ⟨q,h.symm⟩ hys
      have hjy : old A b j ∣ y := (old_dvd_transport_iff hf hg b j y).1
        ((hj' _).1 ⟨⟨q,h.symm⟩,hys⟩)
      exact transport_factor_of_dvd hf hg b (cons A b s Y' hx.2) y q h
        ((Gate.dvd A b hj).trans hjy)

include hB hA hC in
/-- Comparisons between transported probe normal forms reflect. -/
theorem transport_dvd_iff (x y : Word A b) :
    transport hf hg b x ∣ transport hf hg b y ↔ x ∣ y := by
  constructor
  · rintro ⟨q,hq⟩
    obtain ⟨r,hr⟩ := transport_factors hf hg b hB hA hC x y q hq.symm
    exact ⟨r,transport_injective hf hg b (by rw [transport_mul,hr,← hq])⟩
  · exact (transportHom hf hg b).map_dvd

end PartitionConsistency.ProbeAlgebra.Word

namespace PartitionConsistency.ProbeAlgebra.Word
universe u v w z
open DiagramOrder
variable {B : Type u} {M : Type v} {S : Type w} {T : Type z}
  [LeftCancelMonoid B] [IsConical B] [LeftCancelMonoid M] [IsConical M]
  {A : Alphabet B S} {C : Alphabet M T} {f : B →* M} {g : S → T}
  (hf : Conservative f) (hg : AlphabetSimulation A C f g) (b : B) (hb : b ≠ 1)

@[simp] theorem transport_generator (s : S) :
    transport hf hg b (generator A b hb s) =
      generator C (f b) (fun h => hb (hf.injective (h.trans f.map_one.symm))) (g s) := by
  apply Subtype.ext
  change Raw.cons (g s) (Raw.old (f 1)) = Raw.cons (g s) (Raw.old 1)
  rw [f.map_one]

variable (hB : HasConditionalJoins (LeftDivOrder B))
  (hA : Conservative (oldHom A b)) (hC : Conservative (oldHom C (f b)))

include hB hA hC in
omit [IsConical M] in
/-- An old/new common upper bound in the larger extension lies above a
smaller common upper bound. The latter is the new word itself, or is old
and obtained by joining its shared gate with the old divisor. -/
theorem transport_old_common_below (x : B) (y : Word A b) (q : Word C (f b))
    (hx : old C (f b) (f x) ∣ q) (hy : transport hf hg b y ∣ q) :
    ∃ j : Word A b, old A b x ∣ j ∧ y ∣ j ∧ transport hf hg b j ∣ q := by
  classical
  by_cases hxy : old A b x ∣ y
  · exact ⟨y,hxy,dvd_refl y,hy⟩
  cases he : head A b y with
  | none =>
    obtain ⟨a,rfl⟩ := (head_eq_none_iff A b y).1 he
    obtain ⟨j,hxj,haj,hjq⟩ := (hf.comp hC).common_below hB hx hy
    exact ⟨old A b j,(oldHom A b).map_dvd hxj,(oldHom A b).map_dvd haj,hjq⟩
  | some s =>
    have hys : head C (f b) (transport hf hg b y) = some (g s) :=
      (head_transport_eq_some hf hg b y s).2 he
    have hq : head C (f b) q ≠ some (g s) := by
      intro hqs
      exact hxy ((old_dvd_transport_iff hf hg b x y).1
        ((old_dvd_iff_headDiv C (f b) (f x) _).2
          ((headDiv_of_same_head C (f b) hys hqs).2
            ((old_dvd_iff_headDiv C (f b) (f x) _).1 hx))))
    obtain ⟨k,hk,hk'⟩ := exists_simulated_gate_of_exit hf hg b hB hA hC y he hy hq
    obtain ⟨j,hxj,hkj,hjq⟩ := (hf.comp hC).common_below hB hx ((hk' q).1 ⟨hy,hq⟩)
    exact ⟨old A b j,(oldHom A b).map_dvd hxj,
      (Gate.dvd A b hk).trans ((oldHom A b).map_dvd hkj),hjq⟩

include hB hA hC in
omit [IsConical M] in
/-- A larger common multiple in one smaller first-letter block puts the
other, differently headed smaller divisor below the entire smaller block. -/
theorem transport_dvd_of_different_head {x y : Word A b} {s t : S}
    (hx : head A b x = some s) (hy : head A b y = some t) (hst : s ≠ t)
    {q : Word C (f b)} (hyq : transport hf hg b y ∣ q)
    (hq : head C (f b) q = some (g s)) : y ∣ x := by
  have hqt : head C (f b) q ≠ some (g t) := by
    rw [hq]
    exact fun h => hst (hg.injective (Option.some.inj h))
  obtain ⟨j,hj,hj'⟩ := exists_simulated_gate_of_exit hf hg b hB hA hC y hy hyq hqt
  have hjx : old A b j ∣ x := (old_dvd_transport_iff hf hg b j x).1
    ((old_dvd_iff_headDiv C (f b) (f j) _).2
      ((headDiv_of_same_head C (f b) ((head_transport_eq_some hf hg b x s).2 hx) hq).2
        ((old_dvd_iff_headDiv C (f b) (f j) _).1 ((hj' q).1 ⟨hyq,hqt⟩))))
  exact (Gate.dvd A b hj).trans hjx

include hb hB hA hC in
/-- Every larger common upper bound of two simulated words lies above a
smaller common upper bound. This simultaneously conserves joins and the
absence of joins, rather than just comparisons between simulated words. -/
theorem transport_common_below (x y : Word A b) (q : Word C (f b))
    (hxq : transport hf hg b x ∣ q) (hyq : transport hf hg b y ∣ q) :
    ∃ j : Word A b, x ∣ j ∧ y ∣ j ∧ transport hf hg b j ∣ q := by
  classical
  obtain ⟨x,hx⟩ := x
  induction x generalizing y q with
  | old x => exact transport_old_common_below hf hg b hB hA hC x y q hxq hyq
  | cons s Y ih =>
    change Y.reduced A b ∧ ¬ Y.headDiv A b at hx
    let Y' : Word A b := ⟨Y,hx.1⟩
    change transport hf hg b (cons A b s Y' hx.2) ∣ q at hxq
    change ∃ j, cons A b s Y' hx.2 ∣ j ∧ y ∣ j ∧ transport hf hg b j ∣ q
    obtain ⟨y,hy⟩ := y
    cases y with
    | old y =>
      obtain ⟨j,hyj,hxj,hjq⟩ := transport_old_common_below hf hg b hB hA hC
        y (cons A b s Y' hx.2) q hyq hxq
      exact ⟨j,hxj,hyj,hjq⟩
    | cons t Z =>
      change Z.reduced A b ∧ ¬ Z.headDiv A b at hy
      let Z' : Word A b := ⟨Z,hy.1⟩
      change transport hf hg b (cons A b t Z' hy.2) ∣ q at hyq
      change ∃ j, cons A b s Y' hx.2 ∣ j ∧ cons A b t Z' hy.2 ∣ j ∧ transport hf hg b j ∣ q
      by_cases hst : s = t
      · subst t
        let c := generator A b hb s
        let c' := generator C (f b) (fun h => hb (hf.injective (h.trans f.map_one.symm))) (g s)
        have hY : cons A b s Y' hx.2 = c * Y' :=
          (generator_mul_of_not_headDiv A b hb s Y' hx.2).symm
        have hZ : cons A b s Z' hy.2 = c * Z' :=
          (generator_mul_of_not_headDiv A b hb s Z' hy.2).symm
        have hY' : transport hf hg b (cons A b s Y' hx.2) = c' * transport hf hg b Y' := by
          rw [hY,transport_mul,transport_generator]
        have hZ' : transport hf hg b (cons A b s Z' hy.2) = c' * transport hf hg b Z' := by
          rw [hZ,transport_mul,transport_generator]
        rw [hY'] at hxq
        rw [hZ'] at hyq
        obtain ⟨r,rfl⟩ := hxq
        have hZY : transport hf hg b Z' ∣ transport hf hg b Y' * r := by
          apply (left_mul_dvd_iff c' _ _).1
          exact (_root_.mul_assoc c' (transport hf hg b Y') r) ▸ hyq
        obtain ⟨j,hYj,hZj,hjr⟩ := ih Z' (transport hf hg b Y' * r)
          hZY hx.1 (dvd_mul_right _ _)
        refine ⟨c * j,?_,?_,?_⟩
        · rw [hY]; exact mul_dvd_mul_left c hYj
        · rw [hZ]; exact mul_dvd_mul_left c hZj
        · rw [transport_mul,show transport hf hg b c = c' from transport_generator hf hg b hb s,
            _root_.mul_assoc]
          exact mul_dvd_mul_left c' hjr
      · by_cases hqs : head C (f b) q = some (g s)
        · have hvw := transport_dvd_of_different_head hf hg b hB hA hC
            (x := cons A b s Y' hx.2) rfl rfl hst hyq hqs
          exact ⟨cons A b s Y' hx.2,dvd_refl _,hvw,hxq⟩
        by_cases hqt : head C (f b) q = some (g t)
        · have hwv := transport_dvd_of_different_head hf hg b hB hA hC
            (x := cons A b t Z' hy.2) rfl rfl (Ne.symm hst) hxq hqt
          exact ⟨cons A b t Z' hy.2,hwv,dvd_refl _,hyq⟩
        obtain ⟨j,hj,hj'⟩ := exists_simulated_gate_of_exit hf hg b hB hA hC
          (cons A b s Y' hx.2) rfl hxq hqs
        obtain ⟨k,hk,hk'⟩ := exists_simulated_gate_of_exit hf hg b hB hA hC
          (cons A b t Z' hy.2) rfl hyq hqt
        obtain ⟨l,hjl,hkl,hlq⟩ := (hf.comp hC).common_below hB
          ((hj' q).1 ⟨hxq,hqs⟩) ((hk' q).1 ⟨hyq,hqt⟩)
        exact ⟨old A b l,(Gate.dvd A b hj).trans ((oldHom A b).map_dvd hjl),
          (Gate.dvd A b hk).trans ((oldHom A b).map_dvd hkl),hlq⟩

include hb hB hA hC in
/-- Probe normal-form simulation conserves factors, all old cone
intersections, and old nonjoins. -/
theorem transport_conservative : Conservative (transportHom hf hg b) where
  injective := transport_injective hf hg b
  factors := transport_factors hf hg b hB hA hC
  intersections x y j hj q := by
    constructor
    · rintro ⟨hx,hy⟩
      obtain ⟨k,hxk,hyk,hkq⟩ := transport_common_below hf hg b hb hB hA hC x y q hx hy
      exact ((transportHom hf hg b).map_dvd ((hj k).1 ⟨hxk,hyk⟩)).trans hkq
    · intro hq
      have hu := (hj j).2 (dvd_refl j)
      exact ⟨((transportHom hf hg b).map_dvd hu.1).trans hq,
        ((transportHom hf hg b).map_dvd hu.2).trans hq⟩
  common x y h := by
    obtain ⟨q,hx,hy⟩ := h
    obtain ⟨j,hxj,hyj,_⟩ := transport_common_below hf hg b hb hB hA hC x y q hx hy
    exact ⟨j,hxj,hyj⟩

end PartitionConsistency.ProbeAlgebra.Word

namespace PartitionConsistency.ProbeAlgebra.Path
universe u v
open DiagramOrder
variable {B : Type u} {M : Type v} [LeftCancelMonoid B] [IsConical B]
  [LeftCancelMonoid M] [IsConical M] {a e : B} (P : Path B a) (he : e ≠ 1)
  {f : B →* M} (hf : Conservative f) (b : B)

/-- Simulate the identical countable probe presentation over the larger
base; this is a homomorphism of the actual reduced-word extensions. -/
noncomputable def simulation : P.Extension he b →*
    (P.map f).Extension (fun h => he (hf.injective (h.trans f.map_one.symm))) (f b) :=
  Word.transportHom hf (P.alphabetSimulation he hf) b

/-- Probe case of source `lem:mono-simulation`.  It conserves right
factors, whole cone intersections, and the lack of a common right multiple. -/
theorem simulation_conservative
    (hB : HasConditionalJoins (LeftDivOrder B)) (hb : b ≠ 1) :
    Conservative (P.simulation he hf b) :=
  Word.transport_conservative hf (P.alphabetSimulation he hf) b hb hB
    (P.oldHom_conservative he b)
    ((P.map f).oldHom_conservative
      (fun h => he (hf.injective (h.trans f.map_one.symm))) (f b))

@[simp] theorem simulation_old (x : B) :
    P.simulation he hf b (Word.old (P.alphabet he) b x) =
      Word.old ((P.map f).alphabet
        (fun h => he (hf.injective (h.trans f.map_one.symm)))) (f b) (f x) := rfl

@[simp] theorem simulation_probe (hb : b ≠ 1) (i : ℕ) :
    P.simulation he hf b (P.probe he b hb i) =
      (P.map f).probe (fun h => he (hf.injective (h.trans f.map_one.symm))) (f b)
        (fun h => hb (hf.injective (h.trans f.map_one.symm))) i := by
  change Word.transport hf (P.alphabetSimulation he hf) b
    (Word.generator (P.alphabet he) b hb (P.letter i 1)) = _
  simp only [Word.transport_generator, lettersMap_letter, map_one, probe]

end PartitionConsistency.ProbeAlgebra.Path

end OAI
