import OAI.SetTheory.PartitionPrinciple.Definability.GroundPackedRefinementFormulaData
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundStageOneRawNames

namespace OAI

namespace PartitionPilot.Forcing.TransitiveGround

section
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable {T T2 : ZFSet.{u}} (hT : T ∈ M.sets)
variable (valid : ∀ z ∈ T, IsName s z) {valid2 : ∀ z ∈ T2, IsName s z}
variable (indices : NiceRefinementIndexSystem M a s b d ∅ T T2 valid valid2)

include indices in
theorem stageOneRawCollision_iff (C E : L) (U Rf Rc u u' w w' : (M.nameDomain s).names)
    (member : refinementIndexCode ∅ (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
      M.niceRefinementIndices a s b d ∅ T T2 valid) (p : P) :
    stageOneRawCollision M (M.stageOneFormulaData a s b d T T2 valid)
      (refinementIndexCode ∅ (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val)
      u.val.val u'.val.val w.val.val w'.val.val (s.encode p) ↔
      M.stageOneCollisionTest s pairing unions powers separation collection carrier order hT valid Rf Rc u u' w w' p := by
  let cls := M.stageOneClassName s pairing unions powers separation collection carrier order hT valid
  let env : Assignment (M.nameDomain s) 4 := ![cls Rc u, cls Rc u', cls Rf w, cls Rf w']
  have codes : (fun j => (env j).val.val) =
      ![(cls Rc u).val.val, (cls Rc u').val.val, (cls Rf w).val.val, (cls Rf w').val.val] := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))) j
  have forcing := M.stageOneRawForces_iff s pairing unions powers separation collection carrier order
    refinementCollisionFormula p env
  rw [codes] at forcing
  have fields := M.stageOneFormulaData_fields s valid a b d indices C E U Rf Rc member
  constructor
  · rintro ⟨f, ground, body⟩
    obtain ⟨_, _, _, _, ff, fr, bu, bu', aw, aw', forced⟩ := body
    have ef := (fields.2.2.2.1 _).1 ff
    have er := (fields.2.2.2.2 _).1 fr
    change stageOneRawClass M T s.carrier s.conditionOrder (s.encode ⊤) (f 1) u.val.val (f 2) at bu
    change stageOneRawClass M T s.carrier s.conditionOrder (s.encode ⊤) (f 1) u'.val.val (f 3) at bu'
    change stageOneRawClass M T s.carrier s.conditionOrder (s.encode ⊤) (f 0) w.val.val (f 4) at aw
    change stageOneRawClass M T s.carrier s.conditionOrder (s.encode ⊤) (f 0) w'.val.val (f 5) at aw'
    rw [er] at bu bu'
    rw [ef] at aw aw'
    have eb := (M.stageOneRawClass_iff s pairing unions powers separation collection carrier order hT valid Rc u _ (ground 2)).1 bu
    have eb' := (M.stageOneRawClass_iff s pairing unions powers separation collection carrier order hT valid Rc u' _ (ground 3)).1 bu'
    have ea := (M.stageOneRawClass_iff s pairing unions powers separation collection carrier order hT valid Rf w _ (ground 4)).1 aw
    have ea' := (M.stageOneRawClass_iff s pairing unions powers separation collection carrier order hT valid Rf w' _ (ground 5)).1 aw'
    rw [eb, eb', ea, ea'] at forced
    exact forcing.1 forced
  · intro forced
    refine ⟨![Rf.val.val, Rc.val.val, (cls Rc u).val.val, (cls Rc u').val.val,
      (cls Rf w).val.val, (cls Rf w').val.val], ?_, ?_⟩
    · exact Fin.cases Rf.property (Fin.cases Rc.property (Fin.cases (cls Rc u).property
        (Fin.cases (cls Rc u').property (Fin.cases (cls Rf w).property
          (Fin.cases (cls Rf w').property (fun j => Fin.elim0 j))))))
    · refine ⟨M.stageOneClassName_mem_bound s pairing unions powers separation collection carrier order hT valid Rc u,
        M.stageOneClassName_mem_bound s pairing unions powers separation collection carrier order hT valid Rc u',
        M.stageOneClassName_mem_bound s pairing unions powers separation collection carrier order hT valid Rf w,
        M.stageOneClassName_mem_bound s pairing unions powers separation collection carrier order hT valid Rf w',
        (fields.2.2.2.1 _).2 rfl, (fields.2.2.2.2 _).2 rfl, ?_, ?_, ?_, ?_, forcing.2 forced⟩
      · exact (M.stageOneRawClass_iff s pairing unions powers separation collection carrier order hT valid Rc u _ (cls Rc u).property).2 rfl
      · exact (M.stageOneRawClass_iff s pairing unions powers separation collection carrier order hT valid Rc u' _ (cls Rc u').property).2 rfl
      · exact (M.stageOneRawClass_iff s pairing unions powers separation collection carrier order hT valid Rf w _ (cls Rf w).property).2 rfl
      · exact (M.stageOneRawClass_iff s pairing unions powers separation collection carrier order hT valid Rf w' _ (cls Rf w').property).2 rfl

end

section
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u}
variable [PartialOrder P] [OrderTop P] (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
variable {G L : Type u} [Group G] [PartialOrder L]
variable (a : PosetAction G P) (b : Presentation L) (d : PosetAction G L)
variable {T2 : ZFSet.{u}} {valid2 : ∀ z ∈ T2, IsName s z}
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid)

include pairing unions powers separation collection carrier order

omit [OrderTop P] in
private theorem raw_three (phi : SetFormula 3) (p : P) (x y z : (M.nameDomain s).names) :
    stageOneRawForces M s.carrier s.conditionOrder (s.encode p) phi ![x.val.val, y.val.val, z.val.val] ↔
      Forces (M.nameDomain s) phi ![x, y, z] p := by
  have equal : (fun j : Fin 3 => ((![x, y, z] : Assignment (M.nameDomain s) 3) j).val.val) =
      ![x.val.val, y.val.val, z.val.val] := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))) j
  rw [← equal]
  exact M.stageOneRawForces_iff s pairing unions powers separation collection carrier order phi p ![x, y, z]

omit [OrderTop P] in
private theorem raw_four (phi : SetFormula 4) (p : P) (x y z w : (M.nameDomain s).names) :
    stageOneRawForces M s.carrier s.conditionOrder (s.encode p) phi ![x.val.val, y.val.val, z.val.val, w.val.val] ↔
      Forces (M.nameDomain s) phi ![x, y, z, w] p := by
  have equal : (fun j : Fin 4 => ((![x, y, z, w] : Assignment (M.nameDomain s) 4) j).val.val) =
      ![x.val.val, y.val.val, z.val.val, w.val.val] := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))) j
  rw [← equal]
  exact M.stageOneRawForces_iff s pairing unions powers separation collection carrier order phi p ![x, y, z, w]

theorem stageOneRawProfile_iff (E : L) (bu aw : (M.nameDomain s).names) (p : P) :
    let data := M.stageOneFormulaData a s b d T T2 valid
    stageOneRawProfile M (data 7) (data 8) (s.encode p) (data 10) (data 11) (data 13)
      (b.encode E) bu.val.val aw.val.val ↔
      ∀ v : L, E ≤ v → Forces (M.nameDomain s) refinementProfileFormula
        ![bu, aw, M.stageOneVisibilityName s valid a b d base directed system v] p := by
  change stageOneRawProfile M s.carrier s.conditionOrder (s.encode p) b.carrier b.conditionOrder
    (M.stageOneFormulaData a s b d T T2 valid 13) (b.encode E) bu.val.val aw.val.val ↔ _
  constructor
  · intro raw v below
    obtain ⟨V, hV, entry, forced⟩ := raw (b.encode v) (b.encode_mem v)
      ((b.pair_mem_conditionOrder E v).2 below)
    have equal := (M.stageOneFormulaData_visibility s valid a b d (T2 := T2) base directed system v V).1 entry
    subst V
    exact (raw_three M s pairing unions powers separation collection carrier order
      refinementProfileFormula p bu aw (M.stageOneVisibilityName s valid a b d base directed system v)).1 forced
  · intro typed v hv below
    obtain ⟨v, rfl⟩ := (b.mem_carrier v).1 hv
    let V := M.stageOneVisibilityName s valid a b d base directed system v
    refine ⟨V.val.val, V.property, ?_, ?_⟩
    · exact (M.stageOneFormulaData_visibility s valid a b d (T2 := T2) base directed system v V.val.val).2 rfl
    · exact (raw_three M s pairing unions powers separation collection carrier order
        refinementProfileFormula p bu aw V).2 (typed v ((b.pair_mem_conditionOrder E v).1 below))

variable (indices : NiceRefinementIndexSystem M a s b d ∅ T T2 valid valid2)

include indices in
theorem stageOneRawCompatibility_iff (C E : L) (U Rf Rc bu aw : (M.nameDomain s).names) (p : P)
    (member : refinementIndexCode ∅ (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
      M.niceRefinementIndices a s b d ∅ T T2 valid) :
    let data := M.stageOneFormulaData a s b d T T2 valid
    let idx := refinementIndexCode ∅ (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
    stageOneRawCompatibility M (data 7) (data 8) (s.encode p) (data 13) (data 12)
      (b.encode C) idx bu.val.val aw.val.val ↔
      Forces (M.nameDomain s) refinementCompatibilityFormula
        ![aw, M.stageOneVisibilityName s valid a b d base directed system C, bu,
          M.stageOneMapName s pairing unions powers separation collection carrier order hT valid U Rf Rc] p := by
  change stageOneRawCompatibility M s.carrier s.conditionOrder (s.encode p)
    (M.stageOneFormulaData a s b d T T2 valid 13) (M.stageOneFormulaData a s b d T T2 valid 12)
    (b.encode C) (refinementIndexCode ∅ (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val)
    bu.val.val aw.val.val ↔ _
  constructor
  · rintro ⟨V, hV, D, hD, visible, mapped, forced⟩
    have equalV := (M.stageOneFormulaData_visibility s valid a b d (T2 := T2) base directed system C V).1 visible
    have equalD := (M.stageOneFormulaData_map s pairing unions powers separation collection carrier order
      hT valid a b d indices C E U Rf Rc member D).1 mapped
    subst V
    subst D
    exact (raw_four M s pairing unions powers separation collection carrier order
      refinementCompatibilityFormula p aw (M.stageOneVisibilityName s valid a b d base directed system C) bu
      (M.stageOneMapName s pairing unions powers separation collection carrier order hT valid U Rf Rc)).1 forced
  · intro forced
    let V := M.stageOneVisibilityName s valid a b d base directed system C
    let D := M.stageOneMapName s pairing unions powers separation collection carrier order hT valid U Rf Rc
    refine ⟨V.val.val, V.property, D.val.val, D.property, ?_, ?_, ?_⟩
    · exact (M.stageOneFormulaData_visibility s valid a b d (T2 := T2) base directed system C V.val.val).2 rfl
    · exact (M.stageOneFormulaData_map s pairing unions powers separation collection carrier order
        hT valid a b d indices C E U Rf Rc member D.val.val).2 rfl
    · exact (raw_four M s pairing unions powers separation collection carrier order
        refinementCompatibilityFormula p aw V bu D).2 forced

end

section
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (nodes : b.carrier ∈ M.sets)
variable {T T2 : ZFSet.{u}} (hT : T ∈ M.sets)
variable (valid : ∀ z ∈ T, IsName s z) {valid2 : ∀ z ∈ T2, IsName s z}
variable (indices : NiceRefinementIndexSystem M a s b d ∅ T T2 valid valid2)

include nodes indices in
theorem stageOneRawSingle_codes (C E : L) (U Rf Rc u w : (M.nameDomain s).names)
    (member : refinementIndexCode ∅ (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
      M.niceRefinementIndices a s b d ∅ T T2 valid) (p : P) :
    let idx := refinementIndexCode ∅ (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
    let data := M.stageOneFormulaData a s b d T T2 valid
    let bu := (M.stageOneClassName s pairing unions powers separation collection carrier order hT valid Rc u).val.val
    let aw := (M.stageOneClassName s pairing unions powers separation collection carrier order hT valid Rf w).val.val
    stageOneRawSingle M data idx u.val.val w.val.val (s.encode p) ↔
      stageOneRawForces M (data 7) (data 8) (s.encode p) refinementActivityFormula ![u.val.val, w.val.val, U.val.val] ∧
      stageOneRawProfile M (data 7) (data 8) (s.encode p) (data 10) (data 11) (data 13) (b.encode E) bu aw ∧
      stageOneRawCompatibility M (data 7) (data 8) (s.encode p) (data 13) (data 12) (b.encode C) idx bu aw := by
  let data := M.stageOneFormulaData a s b d T T2 valid
  let idx := refinementIndexCode ∅ (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
  let bu := M.stageOneClassName s pairing unions powers separation collection carrier order hT valid Rc u
  let aw := M.stageOneClassName s pairing unions powers separation collection carrier order hT valid Rf w
  have fields := M.stageOneFormulaData_fields s valid a b d indices C E U Rf Rc member
  dsimp only
  constructor
  · rintro ⟨f, ground, body⟩
    obtain ⟨_, _, _, _, fc, fe, fu, ff, fr, coarse, fine, active, profile, compatible⟩ := body
    have ec := (fields.1 _).1 fc
    have ee := (fields.2.1 _).1 fe
    have eu := (fields.2.2.1 _).1 fu
    have ef := (fields.2.2.2.1 _).1 ff
    have er := (fields.2.2.2.2 _).1 fr
    change stageOneRawClass M T s.carrier s.conditionOrder (s.encode ⊤) (f 4) u.val.val (f 5) at coarse
    change stageOneRawClass M T s.carrier s.conditionOrder (s.encode ⊤) (f 3) w.val.val (f 6) at fine
    rw [er] at coarse
    rw [ef] at fine
    have eb := (M.stageOneRawClass_iff s pairing unions powers separation collection carrier order hT valid
      Rc u (f 5) (ground 5)).1 coarse
    have ea := (M.stageOneRawClass_iff s pairing unions powers separation collection carrier order hT valid
      Rf w (f 6) (ground 6)).1 fine
    rw [eu] at active
    rw [ee, eb, ea] at profile
    rw [ec, eb, ea] at compatible
    exact ⟨active, profile, compatible⟩
  · rintro ⟨active, profile, compatible⟩
    refine ⟨![b.encode C, b.encode E, U.val.val, Rf.val.val, Rc.val.val, bu.val.val, aw.val.val], ?_, ?_⟩
    · exact Fin.cases (M.transitive nodes (b.encode_mem C))
        (Fin.cases (M.transitive nodes (b.encode_mem E)) (Fin.cases U.property
          (Fin.cases Rf.property (Fin.cases Rc.property (Fin.cases bu.property
            (Fin.cases aw.property (fun j => Fin.elim0 j)))))))
    · refine ⟨b.encode_mem C, b.encode_mem E,
        M.stageOneClassName_mem_bound s pairing unions powers separation collection carrier order hT valid Rc u,
        M.stageOneClassName_mem_bound s pairing unions powers separation collection carrier order hT valid Rf w,
        (fields.1 _).2 rfl, (fields.2.1 _).2 rfl, (fields.2.2.1 _).2 rfl,
        (fields.2.2.2.1 _).2 rfl, (fields.2.2.2.2 _).2 rfl, ?_, ?_, active, profile, compatible⟩
      · exact (M.stageOneRawClass_iff s pairing unions powers separation collection carrier order hT valid
          Rc u bu.val.val bu.property).2 rfl
      · exact (M.stageOneRawClass_iff s pairing unions powers separation collection carrier order hT valid
          Rf w aw.val.val aw.property).2 rfl

end

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (nodes : b.carrier ∈ M.sets)
variable {T T2 : ZFSet.{u}} (hT : T ∈ M.sets)
variable (valid : ∀ z ∈ T, IsName s z) {valid2 : ∀ z ∈ T2, IsName s z}
variable (indices : NiceRefinementIndexSystem M a s b d ∅ T T2 valid valid2)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid)

include nodes indices in
theorem stageOneRawSingle_iff (C E : L) (U Rf Rc u w : (M.nameDomain s).names)
    (member : refinementIndexCode ∅ (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
      M.niceRefinementIndices a s b d ∅ T T2 valid) (p : P) :
    stageOneRawSingle M (M.stageOneFormulaData a s b d T T2 valid)
      (refinementIndexCode ∅ (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val)
      u.val.val w.val.val (s.encode p) ↔
      M.stageOneSingleTests s pairing unions powers separation collection carrier order hT valid
        a b d base directed system C E U Rf Rc u w p := by
  have meaning := M.stageOneRawSingle_codes a s b d pairing unions powers separation collection
    carrier order nodes hT valid indices C E U Rf Rc u w member p
  let bu := M.stageOneClassName s pairing unions powers separation collection carrier order hT valid Rc u
  let aw := M.stageOneClassName s pairing unions powers separation collection carrier order hT valid Rf w
  have codes : (fun j : Fin 3 => ((![u, w, U] : Assignment (M.nameDomain s) 3) j).val.val) =
      ![u.val.val, w.val.val, U.val.val] := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))) j
  have activity := M.stageOneRawForces_iff s pairing unions powers separation collection carrier order
    refinementActivityFormula p ![u, w, U]
  rw [codes] at activity
  have profile := M.stageOneRawProfile_iff s pairing unions powers separation collection carrier order
    valid a b d (T2 := T2) base directed system E bu aw p
  have compatible := M.stageOneRawCompatibility_iff s pairing unions powers separation collection carrier order
    hT valid a b d base directed system indices C E U Rf Rc bu aw p member
  exact meaning.trans (and_congr activity (and_congr profile compatible))

include nodes indices in
theorem stageOneRawTests_iff (A : ZFSet.{u}) (p : P) :
    stageOneRawTests M (M.stageOneFormulaData a s b d T T2 valid) A (s.encode p) ↔
      M.stageOneTests s pairing unions powers separation collection carrier order hT valid
        a b d base directed system T2 A p := by
  have single := M.stageOneRawSingle_iff a s b d pairing unions powers separation collection
    carrier order nodes hT valid indices base directed system
  have collision := M.stageOneRawCollision_iff a s b d pairing unions powers separation collection
    carrier order hT valid indices
  let lift (r : ZFSet.{u}) (hr : r ∈ T) : (M.nameDomain s).names :=
    ⟨⟨r, valid r hr⟩, M.transitive hT hr⟩
  constructor
  · intro raw C E U Rf Rc
    dsimp only
    intro member
    refine ⟨?_, ?_⟩
    · intro u w hu hw entry
      exact (single C E U Rf Rc u w member p).1
        (raw.1 _ member u.val.val hu w.val.val hw entry)
    · intro u u' w w' hu hu' hw hw' entry entry'
      exact (collision C E U Rf Rc u u' w w' member p).1
        (raw.2 _ member u.val.val hu u'.val.val hu' w.val.val hw w'.val.val hw' entry entry')
  · intro typed
    refine ⟨?_, ?_⟩
    · intro t ht rawU hu rawW hw entry
      obtain ⟨C, E, U, Rf, Rc, rfl⟩ := indices.decoded t ht
      exact (single C E U Rf Rc (lift rawU hu) (lift rawW hw) ht p).2
        ((typed C E U Rf Rc ht).1 (lift rawU hu) (lift rawW hw) hu hw entry)
    · intro t ht rawU hu rawU' hu' rawW hw rawW' hw' entry entry'
      obtain ⟨C, E, U, Rf, Rc, rfl⟩ := indices.decoded t ht
      exact (collision C E U Rf Rc (lift rawU hu) (lift rawU' hu') (lift rawW hw) (lift rawW' hw') ht p).2
        ((typed C E U Rf Rc ht).2 (lift rawU hu) (lift rawU' hu') (lift rawW hw) (lift rawW' hw')
          hu hu' hw hw' entry entry')

end PartitionPilot.Forcing.TransitiveGround

end OAI
