import OAI.SetTheory.PartitionPrinciple.Definability.TaggedGrowthLayerFormulas

namespace OAI

open scoped ZFSet

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace SetFormula

def countableGrowthWitnessFormula {n} (z L birth t N : Fin n) : SetFormula n :=
  let old := suffixIndex n 3
  let field := prefixIndex n 3
  exBlock 3 (BoundedFormula.countableTaggedLayerFormula
    (old z) (field 0) (field 1) (field 2) (old L) (old birth) (old t) (old N)).toFormula

def copyGrowthWitnessFormula {n} (z Qs rs μs L r μ birth t N : Fin n) : SetFormula n :=
  let old := suffixIndex n 10
  let field := prefixIndex n 10
  exBlock 10 (BoundedFormula.copyTaggedLayerFormula (old z)
    (field 0) (field 1) (field 2) (field 3) (field 4) (field 5) (field 6)
    (old Qs) (old rs) (old μs) (old L) (old r) (old μ) (old birth) (old t) (old N)
    (field 7) (field 8) (field 9)).toFormula

def separatedGrowthWitnessFormula {n} (z Qs rs μs L r μ birth t : Fin n) : SetFormula n :=
  let old := suffixIndex n 10
  let field := prefixIndex n 10
  exBlock 10 (BoundedFormula.separatedTaggedLayerFormula (old z)
    (field 0) (field 1) (field 2) (field 3) (field 4) (field 5) (field 6)
    (old Qs) (old rs) (old μs) (old L) (old r) (old μ) (old birth) (old t)
    (field 7) (field 8) (field 9)).toFormula

def growthLayerWitnessFormula {n} (z Qs rs μs L r μ birth t N : Fin n) : SetFormula n :=
  disj (countableGrowthWitnessFormula z L birth t N)
    (disj (copyGrowthWitnessFormula z Qs rs μs L r μ birth t N)
      (separatedGrowthWitnessFormula z Qs rs μs L r μ birth t))
end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

private theorem realize_boundedExBlock {n} (k : Nat) (φ : BoundedFormula (n + k))
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (exBlock k φ.toFormula) env ↔
      ∃ fields : Fin k → ZFSet.{u}, (∀ i, fields i ∈ M.sets) ∧
        BoundedFormula.Truth φ (extendMany k fields env) := by
  rw [realize_exBlock]
  constructor
  · rintro ⟨fields, ground, recognized⟩
    exact ⟨fields, ground, (BoundedFormula.realize_toFormula M φ _
      (extendMany_members k fields env ground members)).1 recognized⟩
  · rintro ⟨fields, ground, recognized⟩
    exact ⟨fields, ground, (BoundedFormula.realize_toFormula M φ _
      (extendMany_members k fields env ground members)).2 recognized⟩

theorem realize_countableGrowthWitnessFormula {n} (z L birth t N : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (countableGrowthWitnessFormula z L birth t N) env ↔
      ∃ D injection, env z = countableLayerWitness D injection ∧
        CountableLayerCode (env L) (env birth) (env t) D (env N) injection := by
  rw [countableGrowthWitnessFormula, M.realize_boundedExBlock _ _ env members]
  constructor
  · rintro ⟨fields, _, recognized⟩
    have meaning := (BoundedFormula.truth_countableTaggedLayerFormula
      (suffixIndex n 3 z) (prefixIndex n 3 0) (prefixIndex n 3 1) (prefixIndex n 3 2)
      (suffixIndex n 3 L) (suffixIndex n 3 birth) (suffixIndex n 3 t) (suffixIndex n 3 N)
      (extendMany 3 fields env)).1 recognized
    simp only [extendMany_prefix, extendMany_suffix] at meaning
    exact ⟨fields 1, fields 2, meaning.2⟩
  · rintro ⟨D, injection, equal, code⟩
    let fields : Fin 3 → ZFSet.{u} := Fin.cases (natSetCode 0) (Fin.cases D (fun _ => injection))
    have hWitness : countableLayerWitness D injection ∈ M.sets := equal ▸ members z
    have ground : ∀ i, fields i ∈ M.sets :=
      M.nonemptyTupleCode_field_mem 2 fields hWitness
    refine ⟨fields, ground, ?_⟩
    apply (BoundedFormula.truth_countableTaggedLayerFormula
      (suffixIndex n 3 z) (prefixIndex n 3 0) (prefixIndex n 3 1) (prefixIndex n 3 2)
      (suffixIndex n 3 L) (suffixIndex n 3 birth) (suffixIndex n 3 t) (suffixIndex n 3 N)
      (extendMany 3 fields env)).2
    simp only [extendMany_prefix, extendMany_suffix]
    exact ⟨rfl, equal, code⟩

theorem realize_copyGrowthWitnessFormula
    (unions : Realize M.sets SetFormula.union Fin.elim0) {n}
    (z Qs rs μs L r μ birth t N : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (copyGrowthWitnessFormula z Qs rs μs L r μ birth t N) env ↔
      ∃ I parts Indices Maps W injection,
        env z = copyLayerWitness I parts Indices Maps W injection ∧
        CopyLayerCode (env Qs) (env rs) (env μs) (env L) (env r) (env μ) (env birth)
          (env t) I parts Indices Maps W (env N) injection := by
  rw [copyGrowthWitnessFormula, M.realize_boundedExBlock _ _ env members]
  constructor
  · rintro ⟨fields, _, recognized⟩
    have meaning := (BoundedFormula.truth_copyTaggedLayerFormula
      (suffixIndex n 10 z) (prefixIndex n 10 0) (prefixIndex n 10 1) (prefixIndex n 10 2)
      (prefixIndex n 10 3) (prefixIndex n 10 4) (prefixIndex n 10 5) (prefixIndex n 10 6)
      (suffixIndex n 10 Qs) (suffixIndex n 10 rs) (suffixIndex n 10 μs) (suffixIndex n 10 L)
      (suffixIndex n 10 r) (suffixIndex n 10 μ) (suffixIndex n 10 birth) (suffixIndex n 10 t)
      (suffixIndex n 10 N) (prefixIndex n 10 7) (prefixIndex n 10 8) (prefixIndex n 10 9)
      (extendMany 10 fields env)).1 recognized
    simp only [extendMany_prefix, extendMany_suffix] at meaning
    exact ⟨fields 1, fields 2, fields 3, fields 4, fields 5, fields 6,
      meaning.2.1, meaning.2.2.2.2.2⟩
  · rintro ⟨I, parts, Indices, Maps, W, injection, equal, code⟩
    let stored : Fin 7 → ZFSet.{u} := Fin.cases (natSetCode 1) (Fin.cases I (Fin.cases parts
      (Fin.cases Indices (Fin.cases Maps (Fin.cases W (fun _ => injection))))))
    have hWitness : nonemptyTupleCode 6 stored ∈ M.sets := by
      change copyLayerWitness I parts Indices Maps W injection ∈ M.sets
      exact equal ▸ members z
    have storedGround := M.nonemptyTupleCode_field_mem 6 stored hWitness
    let fields : Fin 10 → ZFSet.{u} := Fin.cases (natSetCode 1) (Fin.cases I (Fin.cases parts
      (Fin.cases Indices (Fin.cases Maps (Fin.cases W (Fin.cases injection
        (Fin.cases (⋃₀ ⋃₀ env Qs) (Fin.cases (⋃₀ ⋃₀ env rs) (fun _ => ⋃₀ ⋃₀ env μs)))))))))
    have ground : ∀ i, fields i ∈ M.sets :=
      (Fin.cases (storedGround 0) (Fin.cases (storedGround 1) (Fin.cases (storedGround 2) (Fin.cases (storedGround 3) (Fin.cases (storedGround 4) (Fin.cases (storedGround 5) (Fin.cases (storedGround 6) (Fin.cases (M.union_mem unions (M.union_mem unions (members Qs))) (Fin.cases (M.union_mem unions (M.union_mem unions (members rs))) (fun _ => (M.union_mem unions (M.union_mem unions (members μs)))))))))))))
    refine ⟨fields, ground, ?_⟩
    apply (BoundedFormula.truth_copyTaggedLayerFormula
      (suffixIndex n 10 z) (prefixIndex n 10 0) (prefixIndex n 10 1) (prefixIndex n 10 2)
      (prefixIndex n 10 3) (prefixIndex n 10 4) (prefixIndex n 10 5) (prefixIndex n 10 6)
      (suffixIndex n 10 Qs) (suffixIndex n 10 rs) (suffixIndex n 10 μs) (suffixIndex n 10 L)
      (suffixIndex n 10 r) (suffixIndex n 10 μ) (suffixIndex n 10 birth) (suffixIndex n 10 t)
      (suffixIndex n 10 N) (prefixIndex n 10 7) (prefixIndex n 10 8) (prefixIndex n 10 9)
      (extendMany 10 fields env)).2
    simp only [extendMany_prefix, extendMany_suffix]
    exact ⟨rfl, equal, rfl, rfl, rfl, code⟩

theorem realize_separatedGrowthWitnessFormula
    (unions : Realize M.sets SetFormula.union Fin.elim0) {n}
    (z Qs rs μs L r μ birth t : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) (meet : MeetOrderCode (env L) (env r) (env μ)) :
    Realize M.sets (separatedGrowthWitnessFormula z Qs rs μs L r μ birth t) env ↔
      ∃ I Indices Maps W Components F,
        env z = separatedLayerWitness I Indices Maps W Components F ∧
        SeparatedLayerCode (env Qs) (env rs) (env μs) (env L) (env r) (env μ) (env birth)
          (env t) I Indices Maps W Components F := by
  rw [separatedGrowthWitnessFormula, M.realize_boundedExBlock _ _ env members]
  constructor
  · rintro ⟨fields, _, recognized⟩
    have liftedMeet : MeetOrderCode
        (extendMany 10 fields env (suffixIndex n 10 L))
        (extendMany 10 fields env (suffixIndex n 10 r))
        (extendMany 10 fields env (suffixIndex n 10 μ)) := by
      simpa only [extendMany_suffix] using meet
    have meaning := (BoundedFormula.truth_separatedTaggedLayerFormula
      (suffixIndex n 10 z) (prefixIndex n 10 0) (prefixIndex n 10 1) (prefixIndex n 10 2)
      (prefixIndex n 10 3) (prefixIndex n 10 4) (prefixIndex n 10 5) (prefixIndex n 10 6)
      (suffixIndex n 10 Qs) (suffixIndex n 10 rs) (suffixIndex n 10 μs) (suffixIndex n 10 L)
      (suffixIndex n 10 r) (suffixIndex n 10 μ) (suffixIndex n 10 birth) (suffixIndex n 10 t)
      (prefixIndex n 10 7) (prefixIndex n 10 8) (prefixIndex n 10 9)
      (extendMany 10 fields env) liftedMeet).1 recognized
    simp only [extendMany_prefix, extendMany_suffix] at meaning
    exact ⟨fields 1, fields 2, fields 3, fields 4, fields 5, fields 6,
      meaning.2.1, meaning.2.2.2.2.2⟩
  · rintro ⟨I, Indices, Maps, W, Components, F, equal, code⟩
    let stored : Fin 7 → ZFSet.{u} := Fin.cases (natSetCode 2) (Fin.cases I (Fin.cases Indices
      (Fin.cases Maps (Fin.cases W (Fin.cases Components (fun _ => F))))))
    have hWitness : nonemptyTupleCode 6 stored ∈ M.sets := by
      change separatedLayerWitness I Indices Maps W Components F ∈ M.sets
      exact equal ▸ members z
    have storedGround := M.nonemptyTupleCode_field_mem 6 stored hWitness
    let fields : Fin 10 → ZFSet.{u} := Fin.cases (natSetCode 2) (Fin.cases I (Fin.cases Indices
      (Fin.cases Maps (Fin.cases W (Fin.cases Components (Fin.cases F
        (Fin.cases (⋃₀ ⋃₀ env Qs) (Fin.cases (⋃₀ ⋃₀ env rs) (fun _ => ⋃₀ ⋃₀ env μs)))))))))
    have ground : ∀ i, fields i ∈ M.sets :=
      (Fin.cases (storedGround 0) (Fin.cases (storedGround 1) (Fin.cases (storedGround 2) (Fin.cases (storedGround 3) (Fin.cases (storedGround 4) (Fin.cases (storedGround 5) (Fin.cases (storedGround 6) (Fin.cases (M.union_mem unions (M.union_mem unions (members Qs))) (Fin.cases (M.union_mem unions (M.union_mem unions (members rs))) (fun _ => (M.union_mem unions (M.union_mem unions (members μs)))))))))))))
    refine ⟨fields, ground, ?_⟩
    have liftedMeet : MeetOrderCode
        (extendMany 10 fields env (suffixIndex n 10 L))
        (extendMany 10 fields env (suffixIndex n 10 r))
        (extendMany 10 fields env (suffixIndex n 10 μ)) := by
      simpa only [extendMany_suffix] using meet
    apply (BoundedFormula.truth_separatedTaggedLayerFormula
      (suffixIndex n 10 z) (prefixIndex n 10 0) (prefixIndex n 10 1) (prefixIndex n 10 2)
      (prefixIndex n 10 3) (prefixIndex n 10 4) (prefixIndex n 10 5) (prefixIndex n 10 6)
      (suffixIndex n 10 Qs) (suffixIndex n 10 rs) (suffixIndex n 10 μs) (suffixIndex n 10 L)
      (suffixIndex n 10 r) (suffixIndex n 10 μ) (suffixIndex n 10 birth) (suffixIndex n 10 t)
      (prefixIndex n 10 7) (prefixIndex n 10 8) (prefixIndex n 10 9)
      (extendMany 10 fields env) liftedMeet).2
    simp only [extendMany_prefix, extendMany_suffix]
    exact ⟨rfl, equal, rfl, rfl, rfl, code⟩

theorem realize_growthLayerWitnessFormula
    (unions : Realize M.sets SetFormula.union Fin.elim0) {n}
    (z Qs rs μs L r μ birth t N : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) (meet : MeetOrderCode (env L) (env r) (env μ)) :
    Realize M.sets (growthLayerWitnessFormula z Qs rs μs L r μ birth t N) env ↔
      GrowthLayerWitnessCode (env Qs) (env rs) (env μs) (env L) (env r) (env μ)
        (env birth) (env t) (env N) (env z) := by
  rw [growthLayerWitnessFormula, realize_disj, realize_disj,
    M.realize_countableGrowthWitnessFormula z L birth t N env members,
    M.realize_copyGrowthWitnessFormula unions z Qs rs μs L r μ birth t N env members,
    M.realize_separatedGrowthWitnessFormula unions z Qs rs μs L r μ birth t env members meet]
  rfl

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
