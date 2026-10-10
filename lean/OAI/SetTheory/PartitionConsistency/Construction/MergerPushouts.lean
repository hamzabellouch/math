import Mathlib
import OAI.SetTheory.PartitionConsistency.Algebra.MergerCones
import OAI.SetTheory.PartitionConsistency.Construction.SaturatedMonoids

namespace OAI

/-! ## MergerPresentation -/

namespace PartitionConsistency.MergerAlgebra.Word
universe u v w
noncomputable section
variable {M : Type u} {D : Type v} {N : Type w}
  [Monoid M] [RightFreeAction M D] [Monoid N]

/-- Interpretation of an actual merger normal form. New letters are evaluated
in their displayed order; the target is an arbitrary monoid. -/
def evaluate (f : M →* N) (g : D → N) : Word M D → N
  | old x => f x
  | snoc x d => evaluate f g x * g d

variable (f : M →* N) (g : D → N)
  (hg : ∀ d x, g (RightFreeAction.act d x) = g d * f x)

include hg in
theorem evaluate_act (w : Word M D) (x : M) :
    evaluate f g (act w x) = evaluate f g w * f x := by
  cases w with
  | old y => exact f.map_mul y x
  | snoc w d =>
    change evaluate f g w * g (RightFreeAction.act d x) = (evaluate f g w * g d) * f x
    rw [hg,mul_assoc]

include hg in
theorem evaluate_mul (x y : Word M D) :
    evaluate f g (x*y) = evaluate f g x * evaluate f g y := by
  induction y with
  | old y => exact evaluate_act f g hg x y
  | snoc y d ih =>
    change evaluate f g (x*y) * g d = evaluate f g x * (evaluate f g y * g d)
    rw [ih,mul_assoc]

/-- Universal evaluation of merger words for an equivariant interpretation
of the quotient of copies. -/
def liftHom : Word M D →* N where
  toFun := evaluate f g
  map_one' := f.map_one
  map_mul' := evaluate_mul f g hg

@[simp] theorem liftHom_old (x : M) : liftHom f g hg (old x) = f x := rfl

@[simp] theorem liftHom_letter (d : D) :
    liftHom f g hg (snoc (old 1) d) = g d := by
  change f 1 * g d = g d
  rw [f.map_one,one_mul]

/-- Old coefficients and the single-letter words generate the extension.
This asserts uniqueness in arbitrary target monoids, not just conservative
ones. -/
theorem hom_ext (F G : Word M D →* N)
    (ho : ∀ x, F (old x) = G (old x))
    (hn : ∀ d, F (snoc (old 1) d) = G (snoc (old 1) d)) : F = G := by
  apply MonoidHom.ext
  intro w
  induction w with
  | old x => exact ho x
  | snoc w d ih =>
    have he : snoc w d = w * snoc (old 1) d := by
      change snoc w d = snoc (w * 1) d
      rw [mul_one]
    rw [he,F.map_mul,G.map_mul,ih,hn]

end
end PartitionConsistency.MergerAlgebra.Word

namespace PartitionConsistency.DiagramForcing.OverlapPrescription
universe u v
noncomputable section
variable {M : Type u} [LeftCancelMonoid M] {n : ℕ}
  (P : OverlapPrescription M n) (hP : P.Valid)
  {N : Type v} [Monoid N] (f : M →* N) (p : Fin n → N)

/-- Precisely the finite list of merger relations, interpreted in `N`.
Diagonal entries of `start` are ignored, as in the definition of `Rel`.
Reflected joins, nonjoins or injectivity are not required in the target. -/
def Satisfies : Prop :=
  ∀ i j a b, i ≠ j → P.start i j = some (a,b) → p i * f a = p j * f b

variable (hp : P.Satisfies f p)

include hp in
theorem satisfies_rel {z w : Fin n × M} (h : P.Rel z w) :
    p z.1 * f z.2 = p w.1 * f w.2 := by
  obtain ⟨i,x⟩ := z
  obtain ⟨j,y⟩ := w
  by_cases hij : i = j
  · subst j
    exact congrArg (fun t => p i * f t) ((P.rel_same_copy i x y).mp h)
  · simp only [Rel,hij,↓reduceIte] at h
    cases hs : P.start i j with
    | none => simp only [hs] at h
    | some ab =>
      obtain ⟨a,b⟩ := ab
      rw [hs] at h
      obtain ⟨t,rfl,rfl⟩ := h
      change p i * f (a*t) = p j * f (b*t)
      rw [f.map_mul,f.map_mul,← mul_assoc,← mul_assoc,hp i j a b hij hs]

/-- Interpretation of the actual prescribed quotient, not of a free
collection of formal copies. -/
def interpretedCopy : P.Copies hP → N :=
  Quotient.lift (fun z : Fin n × M => p z.1 * f z.2)
    (fun _ _ h => P.satisfies_rel f p hp h)

@[simp] theorem interpretedCopy_copy (i : Fin n) (x : M) :
    P.interpretedCopy hP f p hp (P.copy hP i x) = p i * f x := rfl

@[simp] theorem interpretedCopy_act (d : P.Copies hP) (x : M) :
    P.interpretedCopy hP f p hp (MergerAlgebra.RightFreeAction.act d x) =
      P.interpretedCopy hP f p hp d * f x := by
  induction d using Quotient.inductionOn with
  | h z =>
    change p z.1 * f (z.2*x) = (p z.1*f z.2)*f x
    rw [f.map_mul,mul_assoc]

/-- The merger normal forms have the universal property of the finite
relative monoid presentation used in the countable-base rearrangement. -/
def presentedLift : P.Merger hP →* N :=
  MergerAlgebra.Word.liftHom f (P.interpretedCopy hP f p hp)
    (P.interpretedCopy_act hP f p hp)

@[simp] theorem presentedLift_old (x : M) :
    P.presentedLift hP f p hp (.old x) = f x := rfl

@[simp] theorem presentedLift_root (i : Fin n) :
    P.presentedLift hP f p hp (P.root hP i) = p i := by
  change f 1 * (p i * f 1) = p i
  rw [f.map_one,one_mul,mul_one]

/-- All normal forms are determined by the old elements and the finitely
many roots. This is the uniqueness part needed when comparing reordered
presentations. -/
theorem presentedHom_ext (F G : P.Merger hP →* N)
    (ho : ∀ x, F (.old x) = G (.old x))
    (hn : ∀ i, F (P.root hP i) = G (P.root hP i)) : F = G := by
  apply MergerAlgebra.Word.hom_ext F G ho
  intro d
  induction d using Quotient.inductionOn with
  | h z =>
    change F (.snoc (.old 1) (P.copy hP z.1 z.2)) =
      G (.snoc (.old 1) (P.copy hP z.1 z.2))
    rw [← P.root_mul_old hP z.1 z.2,F.map_mul,G.map_mul,hn,ho]

include hp in
theorem existsUnique_presentedHom :
    ∃! F : P.Merger hP →* N,
      (∀ x, F (.old x) = f x) ∧ (∀ i, F (P.root hP i) = p i) := by
  refine ⟨P.presentedLift hP f p hp,
    ⟨P.presentedLift_old hP f p hp,P.presentedLift_root hP f p hp⟩,?_⟩
  intro F hF
  apply P.presentedHom_ext hP
  · intro x
    exact (hF.1 x).trans (P.presentedLift_old hP f p hp x).symm
  · intro i
    exact (hF.2 i).trans (P.presentedLift_root hP f p hp i).symm

/-- The literal roots satisfy every relation of their relative presentation. -/
theorem roots_satisfy : P.Satisfies MergerAlgebra.Word.oldHom (P.root hP) := by
  intro i j a b hij hab
  apply (P.root_mul_eq_iff hP (i,a) (j,b)).mpr
  simp only [Rel,hij,↓reduceIte,hab]
  exact ⟨1,(mul_one a).symm,(mul_one b).symm⟩

/-- Every homomorphism from a merger, with no conservation assumption,
necessarily satisfies those relations. -/
theorem map_roots_satisfy (F : P.Merger hP →* N) :
    P.Satisfies (F.comp MergerAlgebra.Word.oldHom) (fun i => F (P.root hP i)) := by
  intro i j a b hij hab
  simpa only [MonoidHom.comp_apply,F.map_mul] using
    congrArg F (P.roots_satisfy hP i j a b hij hab)

end
end PartitionConsistency.DiagramForcing.OverlapPrescription


/-! ## SimulationPushout -/

/-! The conservative simulations are also categorical pushouts among *all*
monoids. This supplies the presentation comparison, which alone is not yet
a countable-base rearrangement. -/
namespace PartitionConsistency.MonoidPushout
universe u
noncomputable section
variable {A B C D : Type u} [Monoid A] [Monoid B] [Monoid C] [Monoid D]

structure IsPushout (f : A →* B) (g : A →* C) (i : B →* D) (j : C →* D) : Prop where
  comm : i.comp f = j.comp g
  universal : ∀ {N : Type u} [Monoid N] (b : B →* N) (c : C →* N),
    b.comp f = c.comp g → ∃! t : D →* N, t.comp i = b ∧ t.comp j = c

namespace IsPushout
variable {f : A →* B} {g : A →* C} {i : B →* D} {j : C →* D}
variable (h : IsPushout f g i j)

def lift {N : Type u} [Monoid N] (b : B →* N) (c : C →* N)
    (hc : b.comp f = c.comp g) : D →* N := (h.universal b c hc).choose

@[simp] theorem lift_comp_left {N : Type u} [Monoid N] (b : B →* N) (c : C →* N)
    (hc : b.comp f = c.comp g) : (h.lift b c hc).comp i = b :=
  (h.universal b c hc).choose_spec.1.1

@[simp] theorem lift_comp_right {N : Type u} [Monoid N] (b : B →* N) (c : C →* N)
    (hc : b.comp f = c.comp g) : (h.lift b c hc).comp j = c :=
  (h.universal b c hc).choose_spec.1.2

include h in
theorem hom_ext {N : Type u} [Monoid N] (s t : D →* N)
    (hb : s.comp i = t.comp i) (hc : s.comp j = t.comp j) : s = t := by
  have hsq : (t.comp i).comp f = (t.comp j).comp g := by
    rw [MonoidHom.comp_assoc,MonoidHom.comp_assoc,h.comm]
  obtain ⟨l,hl,hu⟩ := h.universal (t.comp i) (t.comp j) hsq
  exact (hu s ⟨hb,hc⟩).trans (hu t ⟨rfl,rfl⟩).symm

/-- Apexes of two actual pushout squares are isomorphic over both bases. -/
def equiv {E : Type u} [Monoid E] {i' : B →* E} {j' : C →* E}
    (h' : IsPushout f g i' j') : D ≃* E := by
  let F := h.lift i' j' h'.comm
  let G := h'.lift i j h.comm
  have hFG : F.comp G = MonoidHom.id E := by
    apply h'.hom_ext
    · rw [MonoidHom.comp_assoc,h'.lift_comp_left,h.lift_comp_left,MonoidHom.id_comp]
    · rw [MonoidHom.comp_assoc,h'.lift_comp_right,h.lift_comp_right,MonoidHom.id_comp]
  have hGF : G.comp F = MonoidHom.id D := by
    apply h.hom_ext
    · rw [MonoidHom.comp_assoc,h.lift_comp_left,h'.lift_comp_left,MonoidHom.id_comp]
    · rw [MonoidHom.comp_assoc,h.lift_comp_right,h'.lift_comp_right,MonoidHom.id_comp]
  exact
    { F with
      invFun := G
      left_inv := fun x => DFunLike.congr_fun hGF x
      right_inv := fun x => DFunLike.congr_fun hFG x }

@[simp] theorem equiv_comp_left {E : Type u} [Monoid E] {i' : B →* E} {j' : C →* E}
    (h' : IsPushout f g i' j') : (h.equiv h').toMonoidHom.comp i = i' :=
  h.lift_comp_left i' j' h'.comm

@[simp] theorem equiv_comp_right {E : Type u} [Monoid E] {i' : B →* E} {j' : C →* E}
    (h' : IsPushout f g i' j') : (h.equiv h').toMonoidHom.comp j = j' :=
  h.lift_comp_right i' j' h'.comm

end IsPushout
end
end PartitionConsistency.MonoidPushout

namespace PartitionConsistency.DiagramForcing.OverlapPrescription
universe u
noncomputable section
open DiagramOrder MonoidPushout MergerAlgebra
variable {A B : Type u} [LeftCancelMonoid A] [IsConical A] [LeftCancelMonoid B]
  {n : ℕ} (P : OverlapPrescription A n) (hP : P.Valid)
  (hA : HasConditionalJoins (LeftDivOrder A)) {f : A →* B} (hf : Conservative f)

@[simp] theorem mergerSimulation_root (i : Fin n) :
    P.mergerSimulation hP hA hf (P.root hP i) =
      (P.map f).root (P.valid_map hP hA hf) i := by
  change Word.snoc (Word.old (f 1))
    ((P.map f).copy (P.valid_map hP hA hf) i (f 1)) = _
  rw [f.map_one]
  rfl

omit [IsConical A] in
theorem satisfies_map_iff {N : Type u} [Monoid N] (g : B →* N) (p : Fin n → N) :
    (P.map f).Satisfies g p ↔ P.Satisfies (g.comp f) p := by
  constructor
  · intro h i j a b hij hab
    exact h i j (f a) (f b) hij (by simp only [map_start,hab,Option.map_some])
  · intro h i j a b hij hab
    change (P.start i j).map _ = some (a,b) at hab
    cases hs : P.start i j with
    | none => simp only [hs,Option.map_none] at hab; cases hab
    | some ab =>
      simp only [hs,Option.map_some,Option.some.injEq,Prod.mk.injEq] at hab
      rcases hab with ⟨ha,hb⟩
      subst a; subst b
      exact h i j ab.1 ab.2 hij hs

/-- Simulating a finite merger is extension of scalars for its literal
relative presentation. -/
theorem mergerSimulation_pushout :
    IsPushout (Word.oldHom : A →* P.Merger hP) f
      (P.mergerSimulation hP hA hf)
      (Word.oldHom : B →* (P.map f).Merger (P.valid_map hP hA hf)) where
  comm := by ext x; rfl
  universal s t hc := by
    let p (i : Fin n) := s (P.root hP i)
    have hp : (P.map f).Satisfies t p := by
      apply (P.satisfies_map_iff t p).mpr
      rw [← hc]
      exact P.map_roots_satisfy hP s
    let l := (P.map f).presentedLift (P.valid_map hP hA hf) t p hp
    have hlold : l.comp Word.oldHom = t := by ext x; rfl
    have hlnew : l.comp (P.mergerSimulation hP hA hf) = s := by
      apply P.presentedHom_ext hP
      · intro x
        change t (f x) = s (Word.old x)
        exact (DFunLike.congr_fun hc x).symm
      · intro i
        simp only [MonoidHom.comp_apply,mergerSimulation_root,
          l,presentedLift_root,p]
    refine ⟨l,⟨hlnew,hlold⟩,?_⟩
    intro k hk
    apply (P.map f).presentedHom_ext (P.valid_map hP hA hf)
    · intro x
      exact (DFunLike.congr_fun hk.2 x).trans (DFunLike.congr_fun hlold x).symm
    · intro i
      have hki := DFunLike.congr_fun hk.1 (P.root hP i)
      simpa only [MonoidHom.comp_apply,mergerSimulation_root,
        l,presentedLift_root,p] using hki

end
end PartitionConsistency.DiagramForcing.OverlapPrescription

namespace PartitionConsistency.ProbeAlgebra.Path
universe u
noncomputable section
open DiagramOrder MonoidPushout
variable {A B : Type u} [LeftCancelMonoid A] [IsConical A]
  [LeftCancelMonoid B] [IsConical B] {a e : A} (P : Path A a)
  (he : e ≠ 1) {f : A →* B} (hf : Conservative f) (b : A) (hb : b ≠ 1)

include hb in
/-- Simulating an indexed probe is a pushout for exactly its countable
transition and exit presentation. No universal property is assumed. -/
theorem simulation_pushout :
    IsPushout (Word.oldHom (P.alphabet he) b) f (P.simulation he hf b)
      (Word.oldHom ((P.map f).alphabet
        (fun h => he (hf.injective (h.trans f.map_one.symm)))) (f b)) where
  comm := by ext x; rfl
  universal s t hc := by
    let he' : f e ≠ 1 := fun h => he (hf.injective (h.trans f.map_one.symm))
    let hb' : f b ≠ 1 := fun h => hb (hf.injective (h.trans f.map_one.symm))
    let p (i : ℕ) := s (P.probe he b hb i)
    have hco (x : A) : s (Word.old (P.alphabet he) b x) = t (f x) :=
      DFunLike.congr_fun hc x
    have hp : ∀ i, t ((P.map f).factor i (i+1) (Nat.le_succ i)) * p (i+1) = p i := by
      intro i
      rw [map_factor]
      change t (f (P.factor i (i+1) (Nat.le_succ i))) * s (P.probe he b hb (i+1)) =
        s (P.probe he b hb i)
      rw [← hco,← s.map_mul,P.probe_transition he b hb]
    have hpexit : ∀ i, p i * t (f b) = t ((P.map f).terminal i * f e) := by
      intro i
      rw [map_terminal,← f.map_mul,← hco,← hco,← s.map_mul]
      exact congrArg s (P.probe_mul_b he b hb i)
    let l := (P.map f).presentedLift he' (f b) t p (fun i => (hp i).symm) hpexit
    have hlold : l.comp (Word.oldHom ((P.map f).alphabet he') (f b)) = t := by
      ext x; rfl
    have hlnew : l.comp (P.simulation he hf b) = s := by
      apply P.presentedHom_ext he b hb
      · intro x
        exact (hco x).symm
      · intro i
        simp only [MonoidHom.comp_apply,simulation_probe,l,presentedLift_probe,p]
    refine ⟨l,⟨hlnew,hlold⟩,?_⟩
    intro k hk
    apply (P.map f).presentedHom_ext he' (f b) hb'
    · intro x
      exact (DFunLike.congr_fun hk.2 x).trans (DFunLike.congr_fun hlold x).symm
    · intro i
      have hki := DFunLike.congr_fun hk.1 (P.probe he b hb i)
      simpa only [MonoidHom.comp_apply,simulation_probe,l,presentedLift_probe,p] using hki

end
end PartitionConsistency.ProbeAlgebra.Path


/-! ## PushoutPasting -/

/-! Universal-property bookkeeping for moving already selected cells before
omitted cells. These lemmas are about literal monoid pushouts; they do not
assert the existence of a selected subconstruction. -/
namespace PartitionConsistency.MonoidPushout
universe u
noncomputable section
variable {A B C D E F : Type u} [Monoid A] [Monoid B] [Monoid C]
  [Monoid D] [Monoid E] [Monoid F]

namespace IsPushout

/-- Reflection across the diagonal does not change a pushout. -/
theorem flip {f : A →* B} {g : A →* C} {i : B →* D} {j : C →* D}
    (h : IsPushout f g i j) : IsPushout g f j i where
  comm := h.comm.symm
  universal b c hc := by
    obtain ⟨t,ht,hu⟩ := h.universal c b hc.symm
    exact ⟨t,⟨ht.2,ht.1⟩,fun k hk => hu k ⟨hk.2,hk.1⟩⟩

/-- Two adjoining pushout squares give the outer pushout. In the diagram
`A → B → E`, `C → D → F`, the two vertical composites are unchanged. -/
theorem paste {f : A →* B} {g : A →* C} {i : B →* D} {j : C →* D}
    {k : B →* E} {l : D →* F} {m : E →* F}
    (h : IsPushout f g i j) (h' : IsPushout k i m l) :
    IsPushout (k.comp f) g m (l.comp j) where
  comm := by
    rw [← MonoidHom.comp_assoc,h'.comm,MonoidHom.comp_assoc,h.comm,
      MonoidHom.comp_assoc]
  universal b c hc := by
    let d := h.lift (b.comp k) c (by simpa only [MonoidHom.comp_assoc] using hc)
    have hd₁ : d.comp i = b.comp k := h.lift_comp_left _ _ _
    have hd₂ : d.comp j = c := h.lift_comp_right _ _ _
    let t := h'.lift b d hd₁.symm
    have ht₁ : t.comp m = b := h'.lift_comp_left _ _ _
    have ht₂ : t.comp l = d := h'.lift_comp_right _ _ _
    refine ⟨t,⟨ht₁,by rw [← MonoidHom.comp_assoc,ht₂,hd₂]⟩,?_⟩
    intro s hs
    apply h'.hom_ext
    · exact hs.1.trans ht₁.symm
    · rw [ht₂]
      apply h.hom_ext
      · rw [MonoidHom.comp_assoc,← h'.comm,← MonoidHom.comp_assoc,hs.1,hd₁]
      · rw [MonoidHom.comp_assoc,hs.2,hd₂]

/-- Conversely, if the left square and the outer rectangle are pushouts,
then the right square is a pushout. This is the cancellation used after the
selected future cells have been moved in front of one omitted cell. -/
theorem cancel_left {f : A →* B} {g : A →* C} {i : B →* D} {j : C →* D}
    {k : B →* E} {l : D →* F} {m : E →* F}
    (h : IsPushout f g i j) (hc : m.comp k = l.comp i)
    (ho : IsPushout (k.comp f) g m (l.comp j)) : IsPushout k i m l where
  comm := hc
  universal b d hd := by
    have he : b.comp (k.comp f) = (d.comp j).comp g := by
      rw [← MonoidHom.comp_assoc,hd,MonoidHom.comp_assoc,h.comm,
        MonoidHom.comp_assoc]
    let t := ho.lift b (d.comp j) he
    have ht₁ : t.comp m = b := ho.lift_comp_left _ _ _
    have ht₂ : t.comp (l.comp j) = d.comp j := ho.lift_comp_right _ _ _
    have ht : t.comp l = d := by
      apply h.hom_ext
      · rw [MonoidHom.comp_assoc,← hc,← MonoidHom.comp_assoc,ht₁,hd]
      · rw [MonoidHom.comp_assoc,ht₂]
    refine ⟨t,⟨ht₁,ht⟩,?_⟩
    intro s hs
    apply ho.hom_ext
    · exact hs.1.trans ht₁.symm
    · rw [← MonoidHom.comp_assoc,hs.2,← MonoidHom.comp_assoc,ht]

/-- The degenerate cell is also a pushout; no generator is added. -/
theorem of_id (f : A →* B) :
    IsPushout (MonoidHom.id A) f f (MonoidHom.id B) where
  comm := by simp only [MonoidHom.comp_id,MonoidHom.id_comp]
  universal a b h := by
    simp only [MonoidHom.comp_id] at h
    refine ⟨b,⟨h.symm,MonoidHom.comp_id b⟩,?_⟩
    intro t ht
    simpa only [MonoidHom.comp_id] using ht.2

/-- Postcomposing a pushout apex with a fixed monoid isomorphism preserves
its full universal property, not just its conservative embeddings. -/
theorem map_apex {f : A →* B} {g : A →* C} {i : B →* D} {j : C →* D}
    (h : IsPushout f g i j) (e : D ≃* E) :
    IsPushout f g (e.toMonoidHom.comp i) (e.toMonoidHom.comp j) where
  comm := by rw [MonoidHom.comp_assoc,h.comm,MonoidHom.comp_assoc]
  universal b c hc := by
    let t := (h.lift b c hc).comp e.symm.toMonoidHom
    have he (x : D) : t (e x) = h.lift b c hc x :=
      congrArg (h.lift b c hc) (e.symm_apply_apply x)
    have ht₁ : t.comp (e.toMonoidHom.comp i) = b := by
      ext x
      exact (he (i x)).trans (DFunLike.congr_fun (h.lift_comp_left b c hc) x)
    have ht₂ : t.comp (e.toMonoidHom.comp j) = c := by
      ext x
      exact (he (j x)).trans (DFunLike.congr_fun (h.lift_comp_right b c hc) x)
    refine ⟨t,⟨ht₁,ht₂⟩,?_⟩
    intro s hs
    have hh : s.comp e.toMonoidHom = t.comp e.toMonoidHom := by
      apply h.hom_ext
      · simpa only [MonoidHom.comp_assoc] using hs.1.trans ht₁.symm
      · simpa only [MonoidHom.comp_assoc] using hs.2.trans ht₂.symm
    ext x
    obtain ⟨y,rfl⟩ := e.surjective x
    exact DFunLike.congr_fun hh y

end IsPushout
end
end PartitionConsistency.MonoidPushout

end OAI
