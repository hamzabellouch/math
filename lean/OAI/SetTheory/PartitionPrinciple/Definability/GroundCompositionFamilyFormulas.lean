import OAI.SetTheory.PartitionPrinciple.Definability.GroundPairCompositions

namespace OAI

section

namespace PartitionPilot.Forcing

universe u
namespace SetFormula

def compositionFamilyEntryFormula {n} (z K I J B D L Es Ss : Fin n) : SetFormula n :=
  let lift (i : Fin n) := i.succ.succ.succ.succ.succ
  let body := BoundedFormula.conj (.mem 4 (lift I)) (.conj (.mem 3 (lift J))
      (.conj (BoundedFormula.orderedTripleFormula (lift z) 4 3 0)
        (.conj (BoundedFormula.pairMembershipFormula 4 3 (lift K))
          (.conj (BoundedFormula.pairMembershipFormula 3 2 (lift Es))
            (.conj (BoundedFormula.pairMembershipFormula 4 1 (lift Ss))
              (BoundedFormula.compositionGraphFormula 0 (lift B) (lift D) (lift L) 2 1))))))
  ex (ex (ex (ex (ex body.toFormula))))

def compositionFamilyFormula {n} (family K I J B D L Es Ss : Fin n) : SetFormula n :=
  exactSetFormula family
    (compositionFamilyEntryFormula 0 K.succ I.succ J.succ B.succ D.succ L.succ Es.succ Ss.succ)

end SetFormula

namespace TransitiveGround
open SetFormula
variable (M : TransitiveGround.{u})

theorem realize_compositionFamilyEntryFormula {n} (z K I J B D L Es Ss : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (compositionFamilyEntryFormula z K I J B D L Es Ss) env ↔
      env z ∈ M.groundPairCompositions (env K) (env I) (env J) (env B) (env D) (env L) (env Es) (env Ss) := by
  simp only [compositionFamilyEntryFormula, realize_ex]
  constructor
  · rintro ⟨i, hiM, j, hjM, ell, hellM, f, hfM, c, hcM, body⟩
    have extended : ∀ a, extend c (extend f (extend ell (extend j (extend i env)))) a ∈ M.sets :=
      Fin.cases hcM (Fin.cases hfM (Fin.cases hellM (Fin.cases hjM (Fin.cases hiM members))))
    have spec := (BoundedFormula.realize_toFormula M _ _ extended).1 body
    simp only [BoundedFormula.Truth, BoundedFormula.truth_orderedTripleFormula,
      BoundedFormula.truth_pairMembershipFormula, BoundedFormula.truth_compositionGraphFormula] at spec
    change i ∈ env I ∧ j ∈ env J ∧ env z = ZFSet.pair (ZFSet.pair i j) c ∧
      ZFSet.pair i j ∈ env K ∧ ZFSet.pair j ell ∈ env Es ∧ ZFSet.pair i f ∈ env Ss ∧
      c = relationCompose (env B) (env D) (env L) ell f at spec
    obtain ⟨hi, hj, equal, hk, first, second, output⟩ := spec
    rw [equal]
    exact (pair_mem_pairCompositionFamily _ _ _ _ _ _ _ _ _ _ _ _).2
      ⟨hk, hi, hj, (M.mem_groundRelations _ _ _).2
        ⟨hcM, fun w hw => (ZFSet.mem_sep.1 (output ▸ hw)).1⟩, ell, f, first, second, output⟩
  · intro member
    unfold groundPairCompositions pairCompositionFamily at member
    obtain ⟨_, i, hi, j, hj, ell, _, f, _, c, hc, equal, hk, first, second, output⟩ :=
      ZFSet.mem_sep.1 member
    have hiM := M.transitive (members I) hi
    have hjM := M.transitive (members J) hj
    have hellM := M.pair_right (M.transitive (members Es) first)
    have hfM := M.pair_right (M.transitive (members Ss) second)
    have hcM := ((M.mem_groundRelations _ _ _).1 hc).1
    refine ⟨i, hiM, j, hjM, ell, hellM, f, hfM, c, hcM, ?_⟩
    apply (BoundedFormula.realize_toFormula M _ _
      (Fin.cases hcM (Fin.cases hfM (Fin.cases hellM (Fin.cases hjM (Fin.cases hiM members)))))).2
    simp only [BoundedFormula.Truth, BoundedFormula.truth_orderedTripleFormula,
      BoundedFormula.truth_pairMembershipFormula, BoundedFormula.truth_compositionGraphFormula]
    exact ⟨hi, hj, equal, hk, first, second, output⟩

theorem realize_compositionFamilyFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {n} (family K I J B D L Es Ss : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (compositionFamilyFormula family K I J B D L Es Ss) env ↔
      env family = M.groundPairCompositions (env K) (env I) (env J) (env B) (env D) (env L) (env Es) (env Ss) := by
  apply M.realize_exactSetFormula family _ env (members family)
  · intro z member
    unfold groundPairCompositions pairCompositionFamily at member
    obtain ⟨k, hk, c, hc, rfl⟩ := ZFSet.mem_prod.1 (ZFSet.mem_sep.1 member).1
    exact M.orderedPair_mem pairing (M.transitive (members K) hk)
      ((M.mem_groundRelations _ _ _).1 hc).1
  · intro z hz
    exact M.realize_compositionFamilyEntryFormula 0 K.succ I.succ J.succ B.succ D.succ L.succ Es.succ Ss.succ
      (extend z env) (Fin.cases hz members)

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
