import OAI.SetTheory.PartitionPrinciple.Forcing.GroundPushFilters

namespace OAI

section

namespace PartitionPilot.Forcing

open scoped ZFSet

universe u

namespace BoundedFormula

def pairPushFilterEntryFormula {n} (z I J L r Ss Fs B SB FB : Fin n) : BoundedFormula n :=
  exMem I (exMem J.succ (exMem SB.succ.succ (exMem FB.succ.succ.succ
    (exMem B.succ.succ.succ.succ
      (.conj (orderedTripleFormula z.succ.succ.succ.succ.succ 4 3 0)
        (.conj (pairMembershipFormula 4 2 Ss.succ.succ.succ.succ.succ)
          (.conj (pairMembershipFormula 3 1 Fs.succ.succ.succ.succ.succ)
            (pushFilterFormula 0 L.succ.succ.succ.succ.succ r.succ.succ.succ.succ.succ 2 1))))))))

theorem truth_pairPushFilterEntryFormula {n} (z I J L r Ss Fs B SB FB : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (pairPushFilterEntryFormula z I J L r Ss Fs B SB FB) env ↔
      ∃ i ∈ env I, ∃ j ∈ env J, ∃ S ∈ env SB, ∃ F ∈ env FB, ∃ V ∈ env B,
        env z = ZFSet.pair (ZFSet.pair i j) V ∧ ZFSet.pair i S ∈ env Ss ∧
          ZFSet.pair j F ∈ env Fs ∧ V = pushFilterCode (env L) (env r) S F := by
  simp only [pairPushFilterEntryFormula, truth_exMem, Truth,
    truth_orderedTripleFormula, truth_pairMembershipFormula, truth_pushFilterFormula]
  rfl

end BoundedFormula

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem pairPushFilterFamily_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {K I J L rL Ss Fs B : ZFSet.{u}} (hK : K ∈ M.sets) (hI : I ∈ M.sets)
    (hJ : J ∈ M.sets) (hL : L ∈ M.sets) (hrL : rL ∈ M.sets)
    (hSs : Ss ∈ M.sets) (hFs : Fs ∈ M.sets) (hB : B ∈ M.sets) :
    pairPushFilterFamily K I J L rL Ss Fs B ∈ M.sets := by
  have hSB := M.union_mem unions (M.union_mem unions hSs)
  have hFB := M.union_mem unions (M.union_mem unions hFs)
  let params := extend I (extend J (extend L (extend rL (extend Ss (extend Fs
    (extend B (extend (⋃₀ ⋃₀ Ss) (extend (⋃₀ ⋃₀ Fs) Fin.elim0))))))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.pairPushFilterEntryFormula 0 1 2 3 4 5 6 7 8 9) params
    (Fin.cases hI (Fin.cases hJ (Fin.cases hL (Fin.cases hrL (Fin.cases hSs
      (Fin.cases hFs (Fin.cases hB (Fin.cases hSB (Fin.cases hFB (fun i => Fin.elim0 i))))))))))
    (M.prod_mem pairing unions powers separation hK hB)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.pairPushFilterEntryFormula 0 1 2 3 4 5 6 7 8 9) (extend z params))
      (ZFSet.prod K B) = pairPushFilterFamily K I J L rL Ss Fs B := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, pairPushFilterFamily, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_pairPushFilterEntryFormula 0 1 2 3 4 5 6 7 8 9 _)
  exact equal ▸ selected

noncomputable def groundPairPushFilters (K I J L rL Ss Fs : ZFSet.{u}) : ZFSet.{u} :=
  pairPushFilterFamily K I J L rL Ss Fs (M.groundPower L)

theorem groundPairPushFilters_spec
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {K I J L rL Ss Fs : ZFSet.{u}} (hK : K ∈ M.sets) (hI : I ∈ M.sets)
    (hJ : J ∈ M.sets) (hL : L ∈ M.sets) (hrL : rL ∈ M.sets)
    (hSs : Ss ∈ M.sets) (hFs : Fs ∈ M.sets)
    (maps : FunctionGraphOn I Ss) (filters : FunctionGraphOn J Fs) (subset : K ⊆ ZFSet.prod I J) :
    M.groundPairPushFilters K I J L rL Ss Fs ∈ M.sets ∧
      ZFSet.IsFunc K (M.groundPower L) (M.groundPairPushFilters K I J L rL Ss Fs) ∧
      ∀ i j S F V, ZFSet.pair i S ∈ Ss → ZFSet.pair j F ∈ Fs →
        (ZFSet.pair (ZFSet.pair i j) V ∈ M.groundPairPushFilters K I J L rL Ss Fs ↔
          ZFSet.pair i j ∈ K ∧ V = pushFilterCode L rL S F) := by
  have bounded (i j S F : ZFSet.{u}) (mapEntry : ZFSet.pair i S ∈ Ss)
      (filterEntry : ZFSet.pair j F ∈ Fs) : pushFilterCode L rL S F ∈ M.groundPower L :=
    (M.mem_groundPower L _).2
      ⟨M.pushFilterCode_mem separation hL hrL
        (M.pair_right (M.transitive hSs mapEntry)) (M.pair_right (M.transitive hFs filterEntry)),
        pushFilterCode_subset L rL S F⟩
  refine ⟨M.pairPushFilterFamily_mem pairing unions powers separation hK hI hJ hL hrL hSs hFs
    (M.groundPower_mem powers hL),
    pairPushFilterFamily_function subset maps filters
      (fun i _ j _ S F mapEntry filterEntry => bounded i j S F mapEntry filterEntry), ?_⟩
  intro i j S F V mapEntry filterEntry
  rw [groundPairPushFilters, pairPushFilterFamily_entry_iff maps filters mapEntry filterEntry]
  constructor
  · exact fun h => ⟨h.1, h.2.2⟩
  · rintro ⟨hk, rfl⟩
    exact ⟨hk, bounded i j S F mapEntry filterEntry, rfl⟩

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing

universe u
namespace SetFormula

def pushFilterFamilyEntryFormula {n} (z K I J L r Maps Fs : Fin n) : SetFormula n :=
  let lift (i : Fin n) := i.succ.succ.succ.succ.succ
  let body := BoundedFormula.conj (.mem 4 (lift I)) (.conj (.mem 3 (lift J))
      (.conj (BoundedFormula.orderedTripleFormula (lift z) 4 3 0)
        (.conj (BoundedFormula.pairMembershipFormula 4 3 (lift K))
          (.conj (BoundedFormula.pairMembershipFormula 4 2 (lift Maps))
            (.conj (BoundedFormula.pairMembershipFormula 3 1 (lift Fs))
              (BoundedFormula.pushFilterFormula 0 (lift L) (lift r) 2 1))))))
  ex (ex (ex (ex (ex body.toFormula))))

def pushFilterFamilyFormula {n} (family K I J L r Maps Fs : Fin n) : SetFormula n :=
  exactSetFormula family
    (pushFilterFamilyEntryFormula 0 K.succ I.succ J.succ L.succ r.succ Maps.succ Fs.succ)

end SetFormula

namespace TransitiveGround
open SetFormula
variable (M : TransitiveGround.{u})

theorem realize_pushFilterFamilyEntryFormula {n} (z K I J L r Maps Fs : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (pushFilterFamilyEntryFormula z K I J L r Maps Fs) env ↔
      env z ∈ M.groundPairPushFilters (env K) (env I) (env J) (env L) (env r) (env Maps) (env Fs) := by
  simp only [pushFilterFamilyEntryFormula, realize_ex]
  constructor
  · rintro ⟨i, hiM, j, hjM, S, hSM, F, hFM, V, hVM, body⟩
    have extended : ∀ a, extend V (extend F (extend S (extend j (extend i env)))) a ∈ M.sets :=
      Fin.cases hVM (Fin.cases hFM (Fin.cases hSM (Fin.cases hjM (Fin.cases hiM members))))
    have spec := (BoundedFormula.realize_toFormula M _ _ extended).1 body
    simp only [BoundedFormula.Truth, BoundedFormula.truth_orderedTripleFormula,
      BoundedFormula.truth_pairMembershipFormula, BoundedFormula.truth_pushFilterFormula] at spec
    change i ∈ env I ∧ j ∈ env J ∧ env z = ZFSet.pair (ZFSet.pair i j) V ∧
      ZFSet.pair i j ∈ env K ∧ ZFSet.pair i S ∈ env Maps ∧ ZFSet.pair j F ∈ env Fs ∧
      V = pushFilterCode (env L) (env r) S F at spec
    obtain ⟨hi, hj, equal, hk, first, second, output⟩ := spec
    rw [equal]
    exact (pair_mem_pairPushFilterFamily _ _ _ _ _ _ _ _ _ _ _).2
      ⟨hk, (M.mem_groundPower _ _).2 ⟨hVM, output.symm ▸ pushFilterCode_subset _ _ _ _⟩,
        hi, hj, S, F, first, second, output⟩
  · intro member
    unfold groundPairPushFilters pairPushFilterFamily at member
    obtain ⟨_, i, hi, j, hj, S, _, F, _, V, hV, equal, first, second, output⟩ := ZFSet.mem_sep.1 member
    have hk : ZFSet.pair i j ∈ env K := (ZFSet.pair_mem_prod.1 ((equal ▸ (ZFSet.mem_sep.1 member).1))).1
    have hiM := M.transitive (members I) hi
    have hjM := M.transitive (members J) hj
    have hSM := M.pair_right (M.transitive (members Maps) first)
    have hFM := M.pair_right (M.transitive (members Fs) second)
    have hVM := ((M.mem_groundPower _ _).1 hV).1
    refine ⟨i, hiM, j, hjM, S, hSM, F, hFM, V, hVM, ?_⟩
    apply (BoundedFormula.realize_toFormula M _ _
      (Fin.cases hVM (Fin.cases hFM (Fin.cases hSM (Fin.cases hjM (Fin.cases hiM members)))))).2
    simp only [BoundedFormula.Truth, BoundedFormula.truth_orderedTripleFormula,
      BoundedFormula.truth_pairMembershipFormula, BoundedFormula.truth_pushFilterFormula]
    exact ⟨hi, hj, equal, hk, first, second, output⟩

theorem realize_pushFilterFamilyFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {n} (family K I J L r Maps Fs : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (pushFilterFamilyFormula family K I J L r Maps Fs) env ↔
      env family = M.groundPairPushFilters (env K) (env I) (env J) (env L) (env r) (env Maps) (env Fs) := by
  apply M.realize_exactSetFormula family _ env (members family)
  · intro z member
    unfold groundPairPushFilters pairPushFilterFamily at member
    obtain ⟨k, hk, V, hV, rfl⟩ := ZFSet.mem_prod.1 (ZFSet.mem_sep.1 member).1
    exact M.orderedPair_mem pairing (M.transitive (members K) hk) ((M.mem_groundPower _ _).1 hV).1
  · intro z hz
    exact M.realize_pushFilterFamilyEntryFormula 0 K.succ I.succ J.succ L.succ r.succ Maps.succ Fs.succ
      (extend z env) (Fin.cases hz members)

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
