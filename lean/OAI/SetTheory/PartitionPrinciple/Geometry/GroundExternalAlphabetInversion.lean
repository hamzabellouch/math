import OAI.SetTheory.PartitionPrinciple.Definability.TaggedSumPresentations

namespace OAI

section

namespace PartitionPilot.Forcing

open SetRealization
universe u

def externalSymbolInverse {J L : Type u} [Inv J] : J ⊕ (L × Bool) → J ⊕ (L × Bool)
  | .inl g => .inl g⁻¹
  | .inr p => .inr (p.1, !p.2)

theorem externalSymbolInverse_involutive {J L : Type u} [InvolutiveInv J] :
    Function.Involutive (externalSymbolInverse : J ⊕ (L × Bool) → J ⊕ (L × Bool)) := by
  intro x
  cases x with
  | inl g => simp only [externalSymbolInverse, inv_inv]
  | inr p => simp only [externalSymbolInverse, Bool.not_not]

def ExternalSymbolInverseEntry (G S inv x y : ZFSet.{u}) : Prop :=
  (∃ g ∈ G, ∃ h ∈ G, x = externalActorSymbol g ∧ y = externalActorSymbol h ∧
    ZFSet.pair g h ∈ inv) ∨
  ∃ s ∈ S, ∃ b : Bool, x = externalLetterSymbol s b ∧ y = externalLetterSymbol s (!b)

noncomputable def externalSymbolInverseGraph (G S inv : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ x ∈ externalGeneratorAlphabet G S,
    ∃ y ∈ externalGeneratorAlphabet G S, z = ZFSet.pair x y ∧
      ExternalSymbolInverseEntry G S inv x y)
    (ZFSet.prod (externalGeneratorAlphabet G S) (externalGeneratorAlphabet G S))

theorem pair_mem_externalSymbolInverseGraph (G S inv x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ externalSymbolInverseGraph G S inv ↔
      ExternalSymbolInverseEntry G S inv x y := by
  constructor
  · intro h
    obtain ⟨_, x', _, y', _, eq, entry⟩ := ZFSet.mem_sep.1 h
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact entry
  · intro entry
    have bounds : x ∈ externalGeneratorAlphabet G S ∧ y ∈ externalGeneratorAlphabet G S := by
      rcases entry with ⟨g, hg, h, hh, rfl, rfl, _⟩ | ⟨s, hs, b, rfl, rfl⟩
      · exact ⟨(externalActorSymbol_mem G S g).2 hg, (externalActorSymbol_mem G S h).2 hh⟩
      · exact ⟨(externalLetterSymbol_mem G S s b).2 hs,
          (externalLetterSymbol_mem G S s (!b)).2 hs⟩
    exact ZFSet.mem_sep.2 ⟨ZFSet.pair_mem_prod.2 bounds,
      x, bounds.1, y, bounds.2, rfl, entry⟩

theorem externalSymbolInverseGraph_eq_graph {J L : Type u} [Inv J]
    (s : Presentation J) (t : Presentation L) :
    externalSymbolInverseGraph s.carrier t.carrier (s.graph s Inv.inv) =
      (externalGeneratorAlphabetPresentation s t).graph
        (externalGeneratorAlphabetPresentation s t) externalSymbolInverse := by
  apply ZFSet.ext
  intro z
  rw [Presentation.mem_graph]
  constructor
  · intro hz
    obtain ⟨x, _, y, _, rfl⟩ := ZFSet.mem_prod.1 (ZFSet.mem_sep.1 hz).1
    rcases (pair_mem_externalSymbolInverseGraph _ _ _ x y).1 hz with
      ⟨g, hg, h, hh, rfl, rfl, entry⟩ | ⟨a, ha, b, rfl, rfl⟩
    · obtain ⟨g, rfl⟩ := (s.mem_carrier g).1 hg
      obtain ⟨h, rfl⟩ := (s.mem_carrier h).1 hh
      have eq := (s.pair_mem_graph s Inv.inv g h).1 entry
      subst h
      exact ⟨.inl g, rfl⟩
    · obtain ⟨a, rfl⟩ := (t.mem_carrier a).1 ha
      exact ⟨.inr (a, b), rfl⟩
  · rintro ⟨x, rfl⟩
    apply (pair_mem_externalSymbolInverseGraph _ _ _ _ _).2
    cases x with
    | inl g =>
      exact Or.inl ⟨s.encode g, s.encode_mem g, s.encode g⁻¹, s.encode_mem g⁻¹,
        rfl, rfl, (s.pair_mem_graph s Inv.inv g g⁻¹).2 rfl⟩
    | inr p => exact Or.inr ⟨t.encode p.1, t.encode_mem p.1, p.2, rfl, rfl⟩

theorem externalSymbolInverseGraph_entry_iff {J L : Type u} [Inv J]
    (s : Presentation J) (t : Presentation L) (x y : J ⊕ (L × Bool)) :
    ZFSet.pair (externalAlphabetEncode s t x) (externalAlphabetEncode s t y) ∈
      externalSymbolInverseGraph s.carrier t.carrier (s.graph s Inv.inv) ↔
      externalSymbolInverse x = y := by
  rw [externalSymbolInverseGraph_eq_graph]
  exact (externalGeneratorAlphabetPresentation s t).pair_mem_graph _ _ x y

theorem externalSymbolInverseGraph_function {J L : Type u} [Inv J]
    (s : Presentation J) (t : Presentation L) :
    ZFSet.IsFunc (externalGeneratorAlphabet s.carrier t.carrier)
      (externalGeneratorAlphabet s.carrier t.carrier)
      (externalSymbolInverseGraph s.carrier t.carrier (s.graph s Inv.inv)) := by
  rw [externalSymbolInverseGraph_eq_graph]
  exact (externalGeneratorAlphabetPresentation s t).graph_isFunc _ _

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing

open SetFormula
universe u

namespace BoundedFormula

def externalSymbolInverseFormula {n} (x y G S inv zero one : Fin n) : BoundedFormula n :=
  disj
    (exMem G (exMem G.succ
      (.conj (orderedPairFormula x.succ.succ zero.succ.succ 1)
        (.conj (orderedPairFormula y.succ.succ zero.succ.succ 0)
          (pairMembershipFormula 1 0 inv.succ.succ)))))
    (exMem S (disj
      (.conj (orderedRightTripleFormula x.succ one.succ 0 zero.succ)
        (orderedRightTripleFormula y.succ one.succ 0 one.succ))
      (.conj (orderedRightTripleFormula x.succ one.succ 0 one.succ)
        (orderedRightTripleFormula y.succ one.succ 0 zero.succ))))

theorem truth_externalSymbolInverseFormula {n} (x y G S inv zero one : Fin n)
    (env : Fin n → ZFSet.{u}) (hZero : env zero = natSetCode 0)
    (hOne : env one = natSetCode 1) :
    Truth (externalSymbolInverseFormula x y G S inv zero one) env ↔
      ExternalSymbolInverseEntry (env G) (env S) (env inv) (env x) (env y) := by
  simp only [externalSymbolInverseFormula, truth_disj, truth_exMem, Truth,
    truth_orderedPairFormula, truth_pairMembershipFormula, truth_orderedRightTripleFormula]
  change ((∃ g ∈ env G, ∃ h ∈ env G,
    env x = ZFSet.pair (env zero) g ∧ env y = ZFSet.pair (env zero) h ∧
      ZFSet.pair g h ∈ env inv) ∨ ∃ s ∈ env S,
    (env x = ZFSet.pair (env one) (ZFSet.pair s (env zero)) ∧
      env y = ZFSet.pair (env one) (ZFSet.pair s (env one))) ∨
    (env x = ZFSet.pair (env one) (ZFSet.pair s (env one)) ∧
      env y = ZFSet.pair (env one) (ZFSet.pair s (env zero)))) ↔ _
  rw [hZero, hOne]
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨s, hs, h | h⟩
    · exact ⟨s, hs, false, h⟩
    · exact ⟨s, hs, true, h⟩
  · rintro ⟨s, hs, b, h⟩
    cases b with
    | false => exact ⟨s, hs, Or.inl h⟩
    | true => exact ⟨s, hs, Or.inr h⟩

def externalSymbolInverseEntryFormula {n} (z alphabet G S inv zero one : Fin n) :
    BoundedFormula n :=
  exMem alphabet (exMem alphabet.succ
    (.conj (orderedPairFormula z.succ.succ 1 0)
      (externalSymbolInverseFormula 1 0 G.succ.succ S.succ.succ inv.succ.succ
        zero.succ.succ one.succ.succ)))

theorem truth_externalSymbolInverseEntryFormula {n}
    (z alphabet G S inv zero one : Fin n) (env : Fin n → ZFSet.{u})
    (hZero : env zero = natSetCode 0) (hOne : env one = natSetCode 1) :
    Truth (externalSymbolInverseEntryFormula z alphabet G S inv zero one) env ↔
      ∃ x ∈ env alphabet, ∃ y ∈ env alphabet,
        env z = ZFSet.pair x y ∧ ExternalSymbolInverseEntry (env G) (env S) (env inv) x y := by
  simp only [externalSymbolInverseEntryFormula, truth_exMem, Truth, truth_orderedPairFormula]
  apply exists_congr
  intro x
  apply and_congr_right
  intro _
  apply exists_congr
  intro y
  apply and_congr_right
  intro _
  exact and_congr Iff.rfl
    (truth_externalSymbolInverseFormula 1 0 G.succ.succ S.succ.succ inv.succ.succ
      zero.succ.succ one.succ.succ _ hZero hOne)

end BoundedFormula

namespace TransitiveGround

variable (M : TransitiveGround.{u})

theorem externalSymbolInverseGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {G S inv : ZFSet.{u}} (hG : G ∈ M.sets) (hS : S ∈ M.sets) (hInv : inv ∈ M.sets) :
    externalSymbolInverseGraph G S inv ∈ M.sets := by
  have hAlphabet := M.externalGeneratorAlphabet_mem pairing unions powers separation hG hS
  have hZero : natSetCode 0 ∈ M.sets := M.empty_mem ⟨G, hG⟩
  have hOne : natSetCode 1 ∈ M.sets := M.insert_mem pairing unions hZero hZero
  let params := extend (externalGeneratorAlphabet G S) (extend G (extend S (extend inv
    (extend (natSetCode 0) (extend (natSetCode 1) Fin.elim0)))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.externalSymbolInverseEntryFormula 0 1 2 3 4 5 6) params
    (Fin.cases hAlphabet (Fin.cases hG (Fin.cases hS (Fin.cases hInv
      (Fin.cases hZero (Fin.cases hOne (fun i => Fin.elim0 i)))))))
    (M.prod_mem pairing unions powers separation hAlphabet hAlphabet)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.externalSymbolInverseEntryFormula 0 1 2 3 4 5 6) (extend z params))
      (ZFSet.prod (externalGeneratorAlphabet G S) (externalGeneratorAlphabet G S)) =
        externalSymbolInverseGraph G S inv := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, externalSymbolInverseGraph, ZFSet.mem_sep]
    exact and_congr Iff.rfl
      (BoundedFormula.truth_externalSymbolInverseEntryFormula 0 1 2 3 4 5 6 _ rfl rfl)
  exact equal ▸ selected

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
