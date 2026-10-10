import OAI.SetTheory.PartitionPrinciple.Definability.ExternalWordRewriteRealization
import OAI.SetTheory.PartitionPrinciple.Definability.GroundFlatCopyPresentation

namespace OAI

section

namespace PartitionPilot.Forcing.ExternalWordRewrite

open PartitionPilot.Compression.RecursiveMaps.CosetGeometry
universe u
variable (J S : Type u) [Group J]

abbrev WordQuotient := (congruence J S).Quotient

def quotientMap : FreeMonoid (Alphabet J S) →* WordQuotient J S :=
  (congruence J S).mk'

def symbolValue : Alphabet J S → External J S
  | .inl g => old J S g
  | .inr p => signed J S p

def evalWord : FreeMonoid (Alphabet J S) →* External J S := FreeMonoid.lift (symbolValue J S)

theorem atomic_eval {xs ys : List (Alphabet J S)} (h : Atomic xs ys) :
    evalWord J S xs = evalWord J S ys := by
  cases h with
  | old_one => exact (old J S).map_one
  | old_mul g h => exact ((old J S).map_mul g h).symm
  | cancel s b =>
    have cancel : FreeGroup.mk [(s, b), (s, !b)] = (1 : FreeGroup S) :=
      Quot.sound (@FreeGroup.Red.Step.not S [] [] s b)
    change signed J S (s, b) * (signed J S (s, !b) * 1) = 1
    rw [mul_one]
    change free J S (FreeGroup.mk [(s, b)]) * free J S (FreeGroup.mk [(s, !b)]) = 1
    rw [← map_mul, FreeGroup.mul_mk]
    change free J S (FreeGroup.mk [(s, b), (s, !b)]) = 1
    rw [cancel, map_one]

def evalQuotient : WordQuotient J S →* External J S :=
  (congruence J S).lift (evalWord J S)
    (Con.conGen_le.2 (fun _ _ h => atomic_eval J S h))

theorem evalQuotient_mk (xs : List (Alphabet J S)) :
    evalQuotient J S (quotientMap J S xs) = evalWord J S xs := rfl

def oldClass : J →* WordQuotient J S where
  toFun g := quotientMap J S [.inl g]
  map_one' := (Con.eq _).2
    (ConGen.Rel.of (M := FreeMonoid (Alphabet J S)) _ _ Atomic.old_one)
  map_mul' g h := ((Con.eq _).2
    (ConGen.Rel.of (M := FreeMonoid (Alphabet J S)) _ _ (Atomic.old_mul g h))).symm

def freeWordMap : FreeMonoid (S × Bool) →* WordQuotient J S :=
  (quotientMap J S).comp (FreeMonoid.map Sum.inr)

theorem freeWordMap_step {xs ys : List (S × Bool)} (h : FreeGroup.Red.Step xs ys) :
    freeWordMap J S xs = freeWordMap J S ys := by
  cases h with
  | @not pre post s b =>
    apply (Con.eq _).2
    change congruence J S ((pre ++ (s, b) :: (s, !b) :: post).map Sum.inr)
      ((pre ++ post).map Sum.inr)
    have step := ((Atomic.cancel (J := J) s b).step.append_left (pre.map Sum.inr)).append_right
      (post.map Sum.inr)
    simpa only [List.map_append, List.map_cons, List.map_nil, List.append_assoc,
      List.cons_append, List.nil_append] using step.to_congruence

def freeClass : FreeGroup S →* WordQuotient J S where
  toFun := Quot.lift (fun xs => freeWordMap J S xs) (fun _ _ h => freeWordMap_step J S h)
  map_one' := (freeWordMap J S).map_one
  map_mul' := by
    rintro ⟨xs⟩ ⟨ys⟩
    exact (freeWordMap J S).map_mul xs ys

theorem freeClass_mk (xs : List (S × Bool)) :
    freeClass J S (FreeGroup.mk xs) = quotientMap J S (xs.map Sum.inr) := rfl

def fromExternal : External J S →* WordQuotient J S :=
  Monoid.CoprodI.lift (fun b => match b with
    | false => oldClass J S
    | true => freeClass J S)

theorem fromExternal_old (g : J) :
    fromExternal J S (old J S g) = oldClass J S g := rfl

theorem fromExternal_free (x : FreeGroup S) :
    fromExternal J S (free J S x) = freeClass J S x := rfl

theorem fromExternal_evalWord (xs : List (Alphabet J S)) :
    fromExternal J S (evalWord J S xs) = quotientMap J S xs := by
  have hom : (fromExternal J S).comp (evalWord J S) = quotientMap J S := by
    apply FreeMonoid.hom_eq
    intro a
    change fromExternal J S (symbolValue J S a) = quotientMap J S [a]
    cases a with
    | inl g => exact fromExternal_old J S g
    | inr p => exact fromExternal_free J S (FreeGroup.mk [p])
  exact DFunLike.congr_fun hom xs

theorem evalWord_signed_word (xs : List (S × Bool)) :
    evalWord J S (xs.map Sum.inr) = free J S (FreeGroup.mk xs) := by
  induction xs with
  | nil => exact ((free J S).map_one).symm
  | cons p xs ih =>
    have step : evalWord J S ((p :: xs).map Sum.inr) =
        signed J S p * evalWord J S (xs.map Sum.inr) := by
      exact (evalWord J S).map_mul (FreeMonoid.of (.inr p))
        (FreeMonoid.ofList (xs.map Sum.inr))
    rw [step, ih]
    change free J S (FreeGroup.mk [p]) * free J S (FreeGroup.mk xs) =
      free J S (FreeGroup.mk (p :: xs))
    rw [← map_mul, FreeGroup.mul_mk]
    rfl

theorem evalQuotient_fromExternal (x : External J S) :
    evalQuotient J S (fromExternal J S x) = x := by
  induction x using Monoid.CoprodI.induction_on with
  | one => rw [map_one, map_one]
  | of b x =>
    cases b with
    | false =>
      change J at x
      change evalQuotient J S (fromExternal J S (old J S x)) = old J S x
      rw [fromExternal_old]
      change evalWord J S [.inl x] = old J S x
      rfl
    | true =>
      change FreeGroup S at x
      change evalQuotient J S (fromExternal J S (free J S x)) = free J S x
      rw [fromExternal_free]
      induction x using Quot.inductionOn with
      | h xs =>
        change evalQuotient J S (freeClass J S (FreeGroup.mk xs)) = free J S (FreeGroup.mk xs)
        rw [freeClass_mk, evalQuotient_mk]
        exact evalWord_signed_word J S xs
  | mul x y hx hy => simp only [map_mul, hx, hy]

theorem fromExternal_evalQuotient (x : WordQuotient J S) :
    fromExternal J S (evalQuotient J S x) = x := by
  refine Con.induction_on x ?_
  intro xs
  exact fromExternal_evalWord J S xs

def quotientEquiv : WordQuotient J S ≃* External J S where
  toFun := evalQuotient J S
  invFun := fromExternal J S
  left_inv := fromExternal_evalQuotient J S
  right_inv := evalQuotient_fromExternal J S
  map_mul' := (evalQuotient J S).map_mul

theorem path_iff_evalWord (xs ys : List (Alphabet J S)) :
    Path xs ys ↔ evalWord J S xs = evalWord J S ys := by
  constructor
  · intro h
    have eq : quotientMap J S xs = quotientMap J S ys :=
      (Con.eq _).2 ((path_iff_conGen xs ys).1 h)
    exact congrArg (evalQuotient J S) eq
  · intro eq
    apply (path_iff_conGen xs ys).2
    apply (Con.eq _).1
    apply (quotientEquiv J S).injective
    exact eq

theorem evalWord_surjective : Function.Surjective (evalWord J S) := by
  intro x
  obtain ⟨xs, eq⟩ := (Con.mk'_surjective (c := congruence J S)) (fromExternal J S x)
  exact ⟨xs, (congrArg (evalQuotient J S) eq).trans (evalQuotient_fromExternal J S x)⟩

end PartitionPilot.Forcing.ExternalWordRewrite



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def externalWordEquivalence (G S m one : ZFSet.{u}) : ZFSet.{u} :=
  M.finitePathClosure (M.finiteWords (externalGeneratorAlphabet G S)) (M.externalWordSteps G S m one)

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)

include pairing unions powers separation infinite

theorem externalWordEquivalence_mem {G S m one : ZFSet.{u}}
    (hG : G ∈ M.sets) (hS : S ∈ M.sets) (hm : m ∈ M.sets) (hOne : one ∈ M.sets) :
    M.externalWordEquivalence G S m one ∈ M.sets :=
  M.finitePathClosure_mem pairing unions powers separation infinite
    (M.finiteWords_mem pairing unions powers separation infinite
      (M.externalGeneratorAlphabet_mem pairing unions powers separation hG hS))
    (M.externalWordSteps_mem pairing unions powers separation infinite hG hS hm hOne)

theorem externalWordEquivalence_code {G S m one : ZFSet.{u}}
    (hG : G ∈ M.sets) (hS : S ∈ M.sets) :
    EquivalenceRelationCode (M.finiteWords (externalGeneratorAlphabet G S))
      (M.externalWordEquivalence G S m one) := by
  let W := M.finiteWords (externalGeneratorAlphabet G S)
  let p := SetMembers.presentation W
  have hW : W ∈ M.sets := M.finiteWords_mem pairing unions powers separation infinite
    (M.externalGeneratorAlphabet_mem pairing unions powers separation hG hS)
  exact M.finitePathClosure_equivalence pairing unions separation infinite p
    (fun x y => ZFSet.pair (p.encode x) (p.encode y) ∈ M.externalWordSteps G S m one)
    (fun _ _ => Iff.rfl) hW (fun _ _ entry => externalWordStepGraph_symmetric entry)

variable {J L : Type u} [Group J] (s : Presentation J) (t : Presentation L)
variable (hG : s.carrier ∈ M.sets) (hS : t.carrier ∈ M.sets)

include pairing unions powers separation infinite hG hS in
theorem pair_mem_externalWordEquivalence (xs ys : List (J ⊕ (L × Bool))) :
    ZFSet.pair (finiteWordGraph (externalGeneratorAlphabetPresentation s t) xs)
      (finiteWordGraph (externalGeneratorAlphabetPresentation s t) ys) ∈
        M.externalWordEquivalence s.carrier t.carrier
          ((s.product s).graph s (fun p => p.1 * p.2)) (s.encode 1) ↔
      ExternalWordRewrite.Path xs ys := by
  have hAlphabet := M.externalGeneratorAlphabet_mem pairing unions powers separation hG hS
  let a := externalGeneratorAlphabetPresentation s t
  let w := finiteWordPresentation a M pairing unions separation infinite hAlphabet
  exact M.pair_mem_finitePathClosure pairing unions separation infinite w ExternalWordRewrite.Step
    (M.pair_mem_externalWordSteps s t pairing unions separation infinite hAlphabet)
    (M.finiteWords_mem pairing unions powers separation infinite hAlphabet) xs ys

include pairing unions powers separation infinite hG hS in
theorem pair_mem_externalWordEquivalence_eval (xs ys : List (J ⊕ (L × Bool))) :
    ZFSet.pair (finiteWordGraph (externalGeneratorAlphabetPresentation s t) xs)
      (finiteWordGraph (externalGeneratorAlphabetPresentation s t) ys) ∈
        M.externalWordEquivalence s.carrier t.carrier
          ((s.product s).graph s (fun p => p.1 * p.2)) (s.encode 1) ↔
      ExternalWordRewrite.evalWord J L xs = ExternalWordRewrite.evalWord J L ys :=
  (M.pair_mem_externalWordEquivalence pairing unions powers separation infinite s t hG hS xs ys).trans
    (ExternalWordRewrite.path_iff_evalWord J L xs ys)

include pairing unions powers separation infinite hG hS in
theorem pair_mem_externalWordEquivalence_congruence (xs ys : List (J ⊕ (L × Bool))) :
    ZFSet.pair (finiteWordGraph (externalGeneratorAlphabetPresentation s t) xs)
      (finiteWordGraph (externalGeneratorAlphabetPresentation s t) ys) ∈
        M.externalWordEquivalence s.carrier t.carrier
          ((s.product s).graph s (fun p => p.1 * p.2)) (s.encode 1) ↔
      ExternalWordRewrite.congruence J L xs ys :=
  (M.pair_mem_externalWordEquivalence pairing unions powers separation infinite s t hG hS xs ys).trans
    (ExternalWordRewrite.path_iff_conGen xs ys)

noncomputable def externalWordQuotientPresentation : Presentation (ExternalWordRewrite.WordQuotient J L) :=
  let a := externalGeneratorAlphabetPresentation s t
  let hAlphabet := M.externalGeneratorAlphabet_mem pairing unions powers separation hG hS
  let w := finiteWordPresentation a M pairing unions separation infinite hAlphabet
  w.quotientPresentation (ExternalWordRewrite.congruence J L).toSetoid
    (M.externalWordEquivalence_code pairing unions powers separation infinite hG hS)
    (M.pair_mem_externalWordEquivalence_congruence pairing unions powers separation infinite s t hG hS)

theorem externalWordQuotientPresentation_carrier :
    (M.externalWordQuotientPresentation pairing unions powers separation infinite s t hG hS).carrier =
      equivalenceClasses (M.finiteWords (externalGeneratorAlphabet s.carrier t.carrier))
        (M.externalWordEquivalence s.carrier t.carrier
          ((s.product s).graph s (fun p => p.1 * p.2)) (s.encode 1)) := rfl

theorem externalWordQuotientPresentation_encode_mk (xs : List (J ⊕ (L × Bool))) :
    (M.externalWordQuotientPresentation pairing unions powers separation infinite s t hG hS).encode
      (ExternalWordRewrite.quotientMap J L xs) =
        equivalenceClass (M.finiteWords (externalGeneratorAlphabet s.carrier t.carrier))
          (M.externalWordEquivalence s.carrier t.carrier
            ((s.product s).graph s (fun p => p.1 * p.2)) (s.encode 1))
          (finiteWordGraph (externalGeneratorAlphabetPresentation s t) xs) := rfl

theorem externalWordClassifier_eq_graph :
    equivalenceClassifier (M.finiteWords (externalGeneratorAlphabet s.carrier t.carrier))
      (M.externalWordEquivalence s.carrier t.carrier
        ((s.product s).graph s (fun p => p.1 * p.2)) (s.encode 1)) =
      (finiteWordPresentation (externalGeneratorAlphabetPresentation s t) M pairing unions separation infinite
        (M.externalGeneratorAlphabet_mem pairing unions powers separation hG hS)).graph
        (M.externalWordQuotientPresentation pairing unions powers separation infinite s t hG hS)
        (ExternalWordRewrite.quotientMap J L) := by
  exact (finiteWordPresentation (externalGeneratorAlphabetPresentation s t) M
    pairing unions separation infinite
    (M.externalGeneratorAlphabet_mem pairing unions powers separation hG hS)).quotientClassifier_eq_graph
      (ExternalWordRewrite.congruence J L).toSetoid
      (M.externalWordEquivalence_code pairing unions powers separation infinite hG hS)
      (M.pair_mem_externalWordEquivalence_congruence pairing unions powers separation infinite s t hG hS)

theorem externalWordQuotient_ground
    (hm : (s.product s).graph s (fun p => p.1 * p.2) ∈ M.sets) :
    (M.externalWordQuotientPresentation pairing unions powers separation infinite s t hG hS).carrier ∈ M.sets ∧
      equivalenceClassifier (M.finiteWords (externalGeneratorAlphabet s.carrier t.carrier))
        (M.externalWordEquivalence s.carrier t.carrier
          ((s.product s).graph s (fun p => p.1 * p.2)) (s.encode 1)) ∈ M.sets := by
  have hAlphabet := M.externalGeneratorAlphabet_mem pairing unions powers separation hG hS
  have hWords := M.finiteWords_mem pairing unions powers separation infinite hAlphabet
  have hE := M.externalWordEquivalence_mem pairing unions powers separation infinite hG hS hm
    (M.transitive hG (s.encode_mem 1))
  exact ⟨M.equivalenceClasses_mem powers separation hWords hE,
    M.equivalenceClassifier_mem pairing unions powers separation hWords hE⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
