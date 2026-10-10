import OAI.SetTheory.PartitionPrinciple.Definability.FiniteWordMapCodes

namespace OAI

section

namespace PartitionPilot.Forcing

open SetRealization SetFormula
universe u

namespace BoundedFormula

def finiteWordLengthEntryFormula {n} (z omega alphabet words : Fin n) : BoundedFormula n :=
  exMem words (exMem omega.succ
    (.conj (orderedPairFormula z.succ.succ 1 0) (functionFormula 0 alphabet.succ.succ 1)))

theorem truth_finiteWordLengthEntryFormula {n} (z omega alphabet words : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (finiteWordLengthEntryFormula z omega alphabet words) env ↔
      ∃ f ∈ env words, ∃ N ∈ env omega,
        env z = ZFSet.pair f N ∧ ZFSet.IsFunc N (env alphabet) f := by
  simp only [finiteWordLengthEntryFormula, truth_exMem, Truth,
    truth_orderedPairFormula, truth_functionFormula]
  rfl

end BoundedFormula

namespace TransitiveGround

variable (M : TransitiveGround.{u})

noncomputable def finiteWordLengthGraph (A : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ f ∈ M.finiteWords A, ∃ N ∈ ZFSet.omega,
    z = ZFSet.pair f N ∧ ZFSet.IsFunc N A f)
      (ZFSet.prod (M.finiteWords A) ZFSet.omega)

theorem pair_mem_finiteWordLengthGraph (A f N : ZFSet.{u}) :
    ZFSet.pair f N ∈ M.finiteWordLengthGraph A ↔
      f ∈ M.finiteWords A ∧ N ∈ ZFSet.omega ∧ ZFSet.IsFunc N A f := by
  rw [finiteWordLengthGraph, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, g, hg, K, hK, eq, function⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact ⟨hg, hK, function⟩
  · rintro ⟨hf, hN, function⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hf, hN⟩, f, hf, N, hN, rfl, function⟩

theorem finiteWordLengthGraph_function (A : ZFSet.{u}) :
    ZFSet.IsFunc (M.finiteWords A) ZFSet.omega (M.finiteWordLengthGraph A) := by
  refine ⟨fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_⟩
  intro f hf
  obtain ⟨_, n, function⟩ := (M.mem_finiteWords A f).1 hf
  refine ⟨natSetCode n, (M.pair_mem_finiteWordLengthGraph A f _).2
    ⟨hf, natSetCode_mem_omega n, function⟩, ?_⟩
  intro N entry
  obtain ⟨_, hN, other⟩ := (M.pair_mem_finiteWordLengthGraph A f N).1 entry
  obtain ⟨k, rfl⟩ := (mem_omega_iff_natSetCode N).1 hN
  exact congrArg natSetCode (finiteWord_domain_unique other function)

theorem pair_mem_finiteWordLengthGraph_word {B : Type u} (s : Presentation B)
    (xs : List B) (hWord : finiteWordGraph s xs ∈ M.sets) (N : ZFSet.{u}) :
    ZFSet.pair (finiteWordGraph s xs) N ∈ M.finiteWordLengthGraph s.carrier ↔
      N = natSetCode xs.length := by
  rw [M.pair_mem_finiteWordLengthGraph]
  constructor
  · rintro ⟨_, hN, function⟩
    obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode N).1 hN
    exact congrArg natSetCode (finiteWord_domain_unique function (finiteWordGraph_function s xs))
  · intro eq
    subst N
    exact ⟨(M.mem_finiteWords _ _).2 ⟨hWord, xs.length, finiteWordGraph_function s xs⟩,
      natSetCode_mem_omega _, finiteWordGraph_function s xs⟩

theorem finiteWordLengthGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {A : ZFSet.{u}} (hA : A ∈ M.sets) : M.finiteWordLengthGraph A ∈ M.sets := by
  have hOmega := M.omega_mem separation infinite
  have hWords := M.finiteWords_mem pairing unions powers separation infinite hA
  have space := M.prod_mem pairing unions powers separation hWords hOmega
  let params := extend ZFSet.omega (extend A (extend (M.finiteWords A) Fin.elim0))
  have selected := M.separation_mem separation
    (BoundedFormula.finiteWordLengthEntryFormula 0 1 2 3).toFormula params
    (Fin.cases hOmega (Fin.cases hA (Fin.cases hWords (fun j => Fin.elim0 j)))) space
  have correct (z : ZFSet.{u}) (hz : z ∈ M.sets) :
      Realize M.sets (BoundedFormula.finiteWordLengthEntryFormula 0 1 2 3).toFormula
        (extend z params) ↔
      ∃ f ∈ M.finiteWords A, ∃ N ∈ ZFSet.omega,
        z = ZFSet.pair f N ∧ ZFSet.IsFunc N A f :=
    (BoundedFormula.realize_toFormula M _ _
      (Fin.cases hz (Fin.cases hOmega (Fin.cases hA (Fin.cases hWords
        (fun j => Fin.elim0 j)))))).trans
      (BoundedFormula.truth_finiteWordLengthEntryFormula 0 1 2 3 _)
  have eq : ZFSet.sep (fun z => Realize M.sets
      (BoundedFormula.finiteWordLengthEntryFormula 0 1 2 3).toFormula (extend z params))
      (ZFSet.prod (M.finiteWords A) ZFSet.omega) = M.finiteWordLengthGraph A := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, finiteWordLengthGraph, ZFSet.mem_sep]
    exact and_congr_right (fun hz => correct z (M.transitive space hz))
  exact eq ▸ selected

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
