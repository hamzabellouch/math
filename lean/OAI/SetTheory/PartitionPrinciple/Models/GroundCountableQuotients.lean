import OAI.SetTheory.PartitionPrinciple.Definability.TaggedSumPresentations

namespace OAI

namespace PartitionPilot.Forcing

universe u

structure EquivalenceRelationCode (S E : ZFSet.{u}) : Prop where
  shape : E ⊆ ZFSet.prod S S
  refl : ∀ x ∈ S, ZFSet.pair x x ∈ E
  symm : ∀ x y, ZFSet.pair x y ∈ E → ZFSet.pair y x ∈ E
  trans : ∀ x y z, ZFSet.pair x y ∈ E → ZFSet.pair y z ∈ E → ZFSet.pair x z ∈ E

def canonicalRepresentativeProperty (S E c x : ZFSet.{u}) : Prop :=
  ∃ n ∈ ZFSet.omega, ZFSet.pair x n ∈ c ∧
    ∀ y ∈ S, ZFSet.pair x y ∈ E → ∀ m ∈ n, ZFSet.pair y m ∉ c

noncomputable def canonicalRepresentatives (S E c : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (canonicalRepresentativeProperty S E c) S

theorem mem_canonicalRepresentatives (S E c x : ZFSet.{u}) :
    x ∈ canonicalRepresentatives S E c ↔ x ∈ S ∧ canonicalRepresentativeProperty S E c x :=
  ZFSet.mem_sep

theorem canonicalRepresentatives_subset (S E c : ZFSet.{u}) :
    canonicalRepresentatives S E c ⊆ S :=
  fun _ h => (ZFSet.mem_sep.1 h).1

theorem canonical_exists {S E c x : ZFSet.{u}}
    (equivalence : EquivalenceRelationCode S E) (injection : InjectionCode S ZFSet.omega c)
    (hx : x ∈ S) : ∃ y ∈ canonicalRepresentatives S E c, ZFSet.pair x y ∈ E := by
  classical
  let valid : Nat → Prop := fun n => ∃ y ∈ S, ZFSet.pair x y ∈ E ∧ ZFSet.pair y (natSetCode n) ∈ c
  have existsValid : ∃ n, valid n := by
    obtain ⟨a, entry, _⟩ := injection.function.2 x hx
    have aNat := (ZFSet.pair_mem_prod.1 (injection.function.1 entry)).2
    obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode a).1 aNat
    exact ⟨n, x, hx, equivalence.refl x hx, entry⟩
  obtain ⟨y, hy, related, entry⟩ := Nat.find_spec existsValid
  refine ⟨y, (mem_canonicalRepresentatives S E c y).2
    ⟨hy, natSetCode (Nat.find existsValid), natSetCode_mem_omega _, entry, ?_⟩, related⟩
  intro z hz yz m hm smaller
  obtain ⟨k, lower, equal⟩ := (mem_natSetCode m (Nat.find existsValid)).1 hm
  have validK : valid k := ⟨z, hz, equivalence.trans x y z related yz, equal ▸ smaller⟩
  exact Nat.not_lt_of_ge (Nat.find_min' existsValid validK) lower

theorem canonical_equiv_eq {S E c x y : ZFSet.{u}}
    (equivalence : EquivalenceRelationCode S E) (injection : InjectionCode S ZFSet.omega c)
    (hx : x ∈ canonicalRepresentatives S E c) (hy : y ∈ canonicalRepresentatives S E c)
    (related : ZFSet.pair x y ∈ E) : x = y := by
  obtain ⟨xS, n, hn, xn, leastX⟩ := (mem_canonicalRepresentatives S E c x).1 hx
  obtain ⟨yS, m, hm, ym, leastY⟩ := (mem_canonicalRepresentatives S E c y).1 hy
  obtain ⟨k, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
  obtain ⟨l, rfl⟩ := (mem_omega_iff_natSetCode m).1 hm
  rcases lt_trichotomy k l with smaller | equal | larger
  · exact False.elim (leastY x xS (equivalence.symm x y related) (natSetCode k)
      ((natSetCode_mem_iff k l).2 smaller) xn)
  · subst l
    exact injection.injective x y (natSetCode k) xn ym
  · exact False.elim (leastX y yS related (natSetCode l)
      ((natSetCode_mem_iff l k).2 larger) ym)

theorem canonical_exists_unique {S E c x : ZFSet.{u}}
    (equivalence : EquivalenceRelationCode S E) (injection : InjectionCode S ZFSet.omega c)
    (hx : x ∈ S) : ∃! y, y ∈ canonicalRepresentatives S E c ∧ ZFSet.pair x y ∈ E := by
  obtain ⟨y, hy, related⟩ := canonical_exists equivalence injection hx
  refine ⟨y, ⟨hy, related⟩, ?_⟩
  intro z hz
  exact canonical_equiv_eq equivalence injection hz.1 hy
    (equivalence.trans z x y (equivalence.symm x z hz.2) related)

noncomputable def canonicalRepresentativesInjection (S E c : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => z ∈ ZFSet.prod (canonicalRepresentatives S E c) ZFSet.omega) c

theorem canonicalRepresentativesInjection_code {S E c : ZFSet.{u}}
    (injection : InjectionCode S ZFSet.omega c) :
    InjectionCode (canonicalRepresentatives S E c) ZFSet.omega (canonicalRepresentativesInjection S E c) :=
  injection.restrict (canonicalRepresentatives_subset S E c)

namespace BoundedFormula

open SetFormula

def canonicalRepresentativeFormula {n} (x s e c omega : Fin n) : BoundedFormula n :=
  exMem omega (.conj (pairMembershipFormula x.succ 0 c.succ)
    (.allMem s.succ (imp (pairMembershipFormula x.succ.succ 0 e.succ.succ)
      (.allMem 1 (.neg (pairMembershipFormula 1 0 c.succ.succ.succ))))))

theorem truth_canonicalRepresentativeFormula {n} (x s e c omega : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (canonicalRepresentativeFormula x s e c omega) env ↔
      ∃ k ∈ env omega, ZFSet.pair (env x) k ∈ env c ∧
        ∀ y ∈ env s, ZFSet.pair (env x) y ∈ env e → ∀ m ∈ k, ZFSet.pair y m ∉ env c := by
  simp only [canonicalRepresentativeFormula, truth_exMem, Truth, truth_imp, truth_pairMembershipFormula]
  rfl

end BoundedFormula

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem canonicalRepresentatives_mem (separation : SeparationSchema M.sets)
    {S E c : ZFSet.{u}} (hS : S ∈ M.sets) (hE : E ∈ M.sets) (hc : c ∈ M.sets)
    (hOmega : ZFSet.omega ∈ M.sets) : canonicalRepresentatives S E c ∈ M.sets := by
  let params := extend S (extend E (extend c (extend ZFSet.omega Fin.elim0)))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.canonicalRepresentativeFormula 0 1 2 3 4) params
    (Fin.cases hS (Fin.cases hE (Fin.cases hc (Fin.cases hOmega (fun i => Fin.elim0 i))))) hS
  have eq : ZFSet.sep (fun x => BoundedFormula.Truth
      (BoundedFormula.canonicalRepresentativeFormula 0 1 2 3 4) (extend x params)) S =
      canonicalRepresentatives S E c := by
    apply ZFSet.ext
    intro x
    rw [ZFSet.mem_sep, mem_canonicalRepresentatives]
    exact and_congr Iff.rfl (BoundedFormula.truth_canonicalRepresentativeFormula 0 1 2 3 4 _)
  exact eq ▸ selected

theorem canonicalRepresentativesInjection_mem (separation : SeparationSchema M.sets)
    {S E c : ZFSet.{u}} (hS : S ∈ M.sets) (hE : E ∈ M.sets) (hc : c ∈ M.sets)
    (hOmega : ZFSet.omega ∈ M.sets) : canonicalRepresentativesInjection S E c ∈ M.sets :=
  M.injection_restriction_mem separation
    (M.canonicalRepresentatives_mem separation hS hE hc hOmega) hOmega hc

theorem canonicalRepresentatives_spec (separation : SeparationSchema M.sets)
    {S E c : ZFSet.{u}} (hS : S ∈ M.sets) (hE : E ∈ M.sets) (hc : c ∈ M.sets)
    (hOmega : ZFSet.omega ∈ M.sets)
    (equivalence : EquivalenceRelationCode S E) (injection : InjectionCode S ZFSet.omega c) :
    canonicalRepresentatives S E c ∈ M.sets ∧ canonicalRepresentatives S E c ⊆ S ∧
      canonicalRepresentativesInjection S E c ∈ M.sets ∧
      InjectionCode (canonicalRepresentatives S E c) ZFSet.omega (canonicalRepresentativesInjection S E c) ∧
      ∀ x ∈ S, ∃! y, y ∈ canonicalRepresentatives S E c ∧ ZFSet.pair x y ∈ E :=
  ⟨M.canonicalRepresentatives_mem separation hS hE hc hOmega,
    canonicalRepresentatives_subset S E c,
    M.canonicalRepresentativesInjection_mem separation hS hE hc hOmega,
    canonicalRepresentativesInjection_code injection,
    fun _ hx => canonical_exists_unique equivalence injection hx⟩

end TransitiveGround

end PartitionPilot.Forcing

end OAI
