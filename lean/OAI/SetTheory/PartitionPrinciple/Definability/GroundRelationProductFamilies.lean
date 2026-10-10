import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundCountableProducts

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u
namespace BoundedFormula

def relationProductSetFormula {n} (output bound A B C D f g : Fin n) : BoundedFormula n :=
  .conj (.allMem output (relationProductEntryFormula 0 A.succ B.succ C.succ D.succ f.succ g.succ))
    (.allMem bound (imp (relationProductEntryFormula 0 A.succ B.succ C.succ D.succ f.succ g.succ)
      (.mem 0 output.succ)))

theorem truth_relationProductSetFormula {n} (output bound A B C D f g : Fin n)
    (env : Fin n → ZFSet.{u})
    (bound_eq : env bound = ZFSet.prod (ZFSet.prod (env A) (env B)) (ZFSet.prod (env C) (env D))) :
    Truth (relationProductSetFormula output bound A B C D f g) env ↔
      env output = relationProduct (env A) (env B) (env C) (env D) (env f) (env g) := by
  simp only [relationProductSetFormula, Truth, truth_imp, truth_relationProductEntryFormula]
  simp only [extend, Fin.cases_zero, Fin.cases_succ, ← mem_relationProduct]
  change ((∀ z ∈ env output, z ∈ relationProduct (env A) (env B) (env C) (env D) (env f) (env g)) ∧
    (∀ z ∈ env bound, z ∈ relationProduct (env A) (env B) (env C) (env D) (env f) (env g) → z ∈ env output)) ↔ _
  constructor
  · rintro ⟨forward, backward⟩
    apply ZFSet.ext
    intro z
    exact ⟨forward z, fun hz => backward z (bound_eq.symm ▸ (ZFSet.mem_sep.1 hz).1) hz⟩
  · intro equal
    exact ⟨fun _ h => equal ▸ h, fun _ _ h => equal.symm ▸ h⟩

def relationProductFamilyEntryFormula : BoundedFormula 12 :=
  exMem 1 (exMem 3 (exMem 7 (exMem 9
    (.conj (orderedPairFormula 4 3 2) (.conj (pairMembershipFormula 3 1 7)
      (.conj (pairMembershipFormula 3 0 8) (relationProductSetFormula 2 15 11 12 13 14 1 0)))))))

theorem truth_relationProductFamilyEntryFormula
    (z I W F H RF RH A B C D : ZFSet.{u}) :
    Truth relationProductFamilyEntryFormula
      ![z,I,W,F,H,RF,RH,A,B,C,D,ZFSet.prod (ZFSet.prod A B) (ZFSet.prod C D)] ↔
    ∃ x ∈ I, ∃ out ∈ W, ∃ f ∈ RF, ∃ h ∈ RH,
      z = ZFSet.pair x out ∧ ZFSet.pair x f ∈ F ∧ ZFSet.pair x h ∈ H ∧
        out = relationProduct A B C D f h := by
  simp only [relationProductFamilyEntryFormula, truth_exMem, Truth,
    truth_orderedPairFormula, truth_pairMembershipFormula]
  apply exists_congr
  intro x
  apply and_congr_right
  intro _
  apply exists_congr
  intro out
  apply and_congr_right
  intro _
  apply exists_congr
  intro f
  apply and_congr_right
  intro _
  apply exists_congr
  intro h
  apply and_congr_right
  intro _
  exact and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl
    (truth_relationProductSetFormula 2 15 11 12 13 14 1 0 _ rfl)))

end BoundedFormula
namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem familyCodeGraph_relationProducts_mem {G : Type u}
    (t : Presentation G) (A B C D : ZFSet.{u}) (f h : G → ZFSet.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (group : t.carrier ∈ M.sets) (hA : A ∈ M.sets) (hB : B ∈ M.sets)
    (hC : C ∈ M.sets) (hD : D ∈ M.sets)
    (wholeF : familyCodeGraph t.encode f ∈ M.sets)
    (wholeH : familyCodeGraph t.encode h ∈ M.sets) :
    familyCodeGraph t.encode (fun g => relationProduct A B C D (f g) (h g)) ∈ M.sets := by
  let F := familyCodeGraph t.encode f
  let H := familyCodeGraph t.encode h
  let RF := F.sUnion.sUnion
  let RH := H.sUnion.sUnion
  let W := M.groundRelations (ZFSet.prod A B) (ZFSet.prod C D)
  let V := ZFSet.prod (ZFSet.prod A B) (ZFSet.prod C D)
  let result := familyCodeGraph t.encode (fun g => relationProduct A B C D (f g) (h g))
  have hRF : RF ∈ M.sets := M.union_mem unions (M.union_mem unions wholeF)
  have hRH : RH ∈ M.sets := M.union_mem unions (M.union_mem unions wholeH)
  have hAB := M.prod_mem pairing unions powers separation hA hB
  have hCD := M.prod_mem pairing unions powers separation hC hD
  have hV : V ∈ M.sets := M.prod_mem pairing unions powers separation hAB hCD
  have hW : W ∈ M.sets := M.groundRelations_mem pairing unions powers separation hAB hCD
  have fEntry (g : G) := (pair_mem_familyCodeGraph t.encode f t.injective g (f g)).2 rfl
  have hEntry (g : G) := (pair_mem_familyCodeGraph t.encode h t.injective g (h g)).2 rfl
  have fiber (g : G) : relationProduct A B C D (f g) (h g) ∈ W := by
    apply (M.mem_groundRelations _ _ _).2
    exact ⟨M.relationProduct_mem pairing unions powers separation hA hB hC hD
      (M.transitive hRF (pair_second_mem_doubleUnion (fEntry g)))
      (M.transitive hRH (pair_second_mem_doubleUnion (hEntry g))), fun _ hz => (ZFSet.mem_sep.1 hz).1⟩
  let params : Fin 11 → ZFSet.{u} := ![t.carrier,W,F,H,RF,RH,A,B,C,D,V]
  have members : ∀ j, params j ∈ M.sets := Fin.cases group (Fin.cases hW (Fin.cases wholeF
    (Fin.cases wholeH (Fin.cases hRF (Fin.cases hRH (Fin.cases hA (Fin.cases hB
      (Fin.cases hC (Fin.cases hD (Fin.cases hV (fun j => Fin.elim0 j)))))))))))
  have meaning (z : ZFSet.{u}) :
      BoundedFormula.Truth BoundedFormula.relationProductFamilyEntryFormula (extend z params) ↔ z ∈ result := by
    change BoundedFormula.Truth BoundedFormula.relationProductFamilyEntryFormula
      ![z,t.carrier,W,F,H,RF,RH,A,B,C,D,ZFSet.prod (ZFSet.prod A B) (ZFSet.prod C D)] ↔ z ∈ result
    rw [BoundedFormula.truth_relationProductFamilyEntryFormula]
    constructor
    · rintro ⟨x,hx,out,_,first,_,second,_,equal,fe,he,product⟩
      obtain ⟨g,rfl⟩ := (t.mem_carrier x).1 hx
      have ef := (pair_mem_familyCodeGraph t.encode f t.injective g first).1 fe
      have eh := (pair_mem_familyCodeGraph t.encode h t.injective g second).1 he
      exact (mem_familyCodeGraph _ _ z).2 ⟨g, by simpa only [ef,eh,product] using equal.symm⟩
    · intro member
      obtain ⟨g,rfl⟩ := (mem_familyCodeGraph _ _ z).1 member
      exact ⟨t.encode g,t.encode_mem g,_,fiber g,f g,pair_second_mem_doubleUnion (fEntry g),
        h g,pair_second_mem_doubleUnion (hEntry g),rfl,fEntry g,hEntry g,rfl⟩
  have bound : result ⊆ ZFSet.prod t.carrier W := by
    intro z hz
    obtain ⟨g,rfl⟩ := (mem_familyCodeGraph _ _ z).1 hz
    exact ZFSet.pair_mem_prod.2 ⟨t.encode_mem g,fiber g⟩
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth BoundedFormula.relationProductFamilyEntryFormula
      (extend z params)) (ZFSet.prod t.carrier W) = result := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, meaning]
    exact ⟨And.right, fun hz => ⟨bound hz,hz⟩⟩
  change result ∈ M.sets
  rw [← equal]
  exact M.bounded_separation_mem separation BoundedFormula.relationProductFamilyEntryFormula
    params members (M.prod_mem pairing unions powers separation group hW)

end TransitiveGround
end PartitionPilot.Forcing

end

end OAI
