import OAI.SetTheory.PartitionPrinciple.Geometry.GroundExternalRewriteSteps

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u
variable {J L : Type u} [Group J] (s : Presentation J) (t : Presentation L)

theorem externalWordAtomicCode_iff (xs ys : List (J ⊕ (L × Bool))) :
    ExternalWordAtomicCode s.carrier t.carrier
      ((s.product s).graph s (fun p => p.1 * p.2)) (s.encode 1)
      (finiteWordGraph (externalGeneratorAlphabetPresentation s t) xs)
      (finiteWordGraph (externalGeneratorAlphabetPresentation s t) ys) ↔
      ExternalWordRewrite.Atomic xs ys := by
  let a := externalGeneratorAlphabetPresentation s t
  have oldOne (g : J) : finiteWordGraph a [.inl g] = wordSingleton (externalActorSymbol (s.encode g)) :=
    finiteWordGraph_singleton a _
  have oldTwo (g h : J) : finiteWordGraph a [.inl g, .inl h] =
      wordDouble (externalActorSymbol (s.encode g)) (externalActorSymbol (s.encode h)) :=
    finiteWordGraph_double a _ _
  have signedTwo (l : L) (b c : Bool) : finiteWordGraph a [.inr (l, b), .inr (l, c)] =
      wordDouble (externalLetterSymbol (t.encode l) b) (externalLetterSymbol (t.encode l) c) :=
    finiteWordGraph_double a _ _
  constructor
  · intro atomic
    rcases atomic with ⟨_, left, right⟩ | ⟨g, hg, h, hh, k, hk, product, left, right⟩ |
      ⟨l, hl, left, right⟩
    · have xsEq := finiteWordGraph_injective a (left.trans (oldOne 1).symm)
      have ysEq := finiteWordGraph_injective a (right.trans (finiteWordGraph_nil a).symm)
      subst xs ys
      exact .old_one
    · obtain ⟨g, rfl⟩ := (s.mem_carrier g).1 hg
      obtain ⟨h, rfl⟩ := (s.mem_carrier h).1 hh
      obtain ⟨k, rfl⟩ := (s.mem_carrier k).1 hk
      have productEq := ((s.product s).pair_mem_graph s (fun p => p.1 * p.2) (g, h) k).1 product
      have xsEq := finiteWordGraph_injective a (left.trans (oldTwo g h).symm)
      have ysEq := finiteWordGraph_injective a (right.trans (oldOne k).symm)
      subst xs ys k
      exact .old_mul g h
    · obtain ⟨l, rfl⟩ := (t.mem_carrier l).1 hl
      have ysEq := finiteWordGraph_injective a (right.trans (finiteWordGraph_nil a).symm)
      subst ys
      rcases left with left | left
      · have xsEq := finiteWordGraph_injective a (left.trans (signedTwo l false true).symm)
        subst xs
        exact .cancel l false
      · have xsEq := finiteWordGraph_injective a (left.trans (signedTwo l true false).symm)
        subst xs
        exact .cancel l true
  · intro atomic
    cases atomic with
    | old_one => exact Or.inl ⟨s.encode_mem 1, oldOne 1, finiteWordGraph_nil a⟩
    | old_mul g h =>
      exact Or.inr (Or.inl ⟨s.encode g, s.encode_mem g, s.encode h, s.encode_mem h,
        s.encode (g * h), s.encode_mem (g * h),
        ((s.product s).pair_mem_graph s (fun p => p.1 * p.2) (g, h) (g * h)).2 rfl,
        oldTwo g h, oldOne (g * h)⟩)
    | cancel l b =>
      refine Or.inr (Or.inr ⟨t.encode l, t.encode_mem l, ?_, finiteWordGraph_nil a⟩)
      cases b
      · exact Or.inl (signedTwo l false true)
      · exact Or.inr (signedTwo l true false)

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (hAlphabet : (externalGeneratorAlphabetPresentation s t).carrier ∈ M.sets)

include pairing unions separation infinite hAlphabet

theorem externalWordStepCode_iff (xs ys : List (J ⊕ (L × Bool))) :
    ExternalWordStepCode (M.finiteWords (externalGeneratorAlphabet s.carrier t.carrier))
      (M.finiteWordAppendGraph (externalGeneratorAlphabet s.carrier t.carrier))
      s.carrier t.carrier ((s.product s).graph s (fun p => p.1 * p.2)) (s.encode 1)
      (finiteWordGraph (externalGeneratorAlphabetPresentation s t) xs)
      (finiteWordGraph (externalGeneratorAlphabetPresentation s t) ys) ↔
      ExternalWordRewrite.Step xs ys := by
  let a := externalGeneratorAlphabetPresentation s t
  have word (v : List (J ⊕ (L × Bool))) :=
    finiteWordGraph_mem_finiteWords a M pairing unions separation infinite hAlphabet v
  have decode (v : ZFSet.{u}) := finiteWords_exact_lists a M pairing unions separation infinite hAlphabet v
  have append (v w : List (J ⊕ (L × Bool))) :
      ZFSet.pair (ZFSet.pair (finiteWordGraph a v) (finiteWordGraph a w))
        (finiteWordGraph a (v ++ w)) ∈ M.finiteWordAppendGraph a.carrier :=
    (M.pair_mem_finiteWordAppendGraph _ _ _ _).2
      ⟨word v, word w, word (v ++ w), finiteWordGraph_append_code a v w⟩
  have appendEq (v w z : List (J ⊕ (L × Bool)))
      (entry : ZFSet.pair (ZFSet.pair (finiteWordGraph a v) (finiteWordGraph a w))
        (finiteWordGraph a z) ∈ M.finiteWordAppendGraph a.carrier) : z = v ++ w :=
    finiteWordGraph_injective a ((finiteWordAppendCode_iff a v w _).1
      ((M.pair_mem_finiteWordAppendGraph _ _ _ _).1 entry).2.2.2)
  constructor
  · rintro ⟨pre, hp, post, hq, l, hl, r, hr, pl, _, pr, _, atomic, left, right, direction⟩
    obtain ⟨pre, rfl⟩ := (decode pre).1 hp
    obtain ⟨post, rfl⟩ := (decode post).1 hq
    obtain ⟨l, rfl⟩ := (decode l).1 hl
    obtain ⟨r, rfl⟩ := (decode r).1 hr
    have leftEq := (finiteWordAppendCode_iff a pre l pl).1
      ((M.pair_mem_finiteWordAppendGraph _ _ _ _).1 left).2.2.2
    have rightEq := (finiteWordAppendCode_iff a pre r pr).1
      ((M.pair_mem_finiteWordAppendGraph _ _ _ _).1 right).2.2.2
    subst pl pr
    refine ⟨pre, post, l, r, (externalWordAtomicCode_iff s t l r).1 atomic, ?_⟩
    rcases direction with ⟨first, second⟩ | ⟨first, second⟩
    · exact Or.inl ⟨appendEq _ _ _ first, appendEq _ _ _ second⟩
    · exact Or.inr ⟨appendEq _ _ _ first, appendEq _ _ _ second⟩
  · rintro ⟨pre, post, l, r, atomic, direction⟩
    refine ⟨finiteWordGraph a pre, word pre, finiteWordGraph a post, word post,
      finiteWordGraph a l, word l, finiteWordGraph a r, word r,
      finiteWordGraph a (pre ++ l), word (pre ++ l),
      finiteWordGraph a (pre ++ r), word (pre ++ r),
      (externalWordAtomicCode_iff s t l r).2 atomic, append pre l, append pre r, ?_⟩
    rcases direction with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨append (pre ++ l) post, append (pre ++ r) post⟩
    · exact Or.inr ⟨append (pre ++ l) post, append (pre ++ r) post⟩

theorem pair_mem_externalWordSteps (xs ys : List (J ⊕ (L × Bool))) :
    ZFSet.pair (finiteWordGraph (externalGeneratorAlphabetPresentation s t) xs)
      (finiteWordGraph (externalGeneratorAlphabetPresentation s t) ys) ∈
        M.externalWordSteps s.carrier t.carrier ((s.product s).graph s (fun p => p.1 * p.2)) (s.encode 1) ↔
      ExternalWordRewrite.Step xs ys := by
  rw [externalWordSteps, pair_mem_externalWordStepGraph,
    M.externalWordStepCode_iff s t pairing unions separation infinite hAlphabet xs ys]
  exact ⟨fun h => h.2.2, fun h => ⟨
    finiteWordGraph_mem_finiteWords _ M pairing unions separation infinite hAlphabet xs,
    finiteWordGraph_mem_finiteWords _ M pairing unions separation infinite hAlphabet ys, h⟩⟩

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
