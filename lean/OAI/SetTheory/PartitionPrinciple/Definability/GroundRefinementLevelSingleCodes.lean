import OAI.SetTheory.PartitionPrinciple.Geometry.GroundPreparedPositionCollisions

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (level : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (nodes : b.carrier ∈ M.sets)
variable {T T2 : ZFSet.{u}} (hT : T ∈ M.sets)
variable (valid : ∀ z ∈ T, IsName s z) {valid2 : ∀ z ∈ T2, IsName s z}
variable (indices : NiceRefinementIndexSystem M a s b d level T T2 valid valid2)

include nodes indices in
theorem refinementLevelRawSingle_codes (C E : L) (U Rf Rc u w : (M.nameDomain s).names)
    (member : refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
      M.niceRefinementIndices a s b d level T T2 valid) (p : P) :
    let idx := refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
    let data := M.refinementLevelFormulaData a s b d level T T2 valid
    let bu := (M.stageOneClassName s pairing unions powers separation collection carrier order hT valid Rc u).val.val
    let aw := (M.stageOneClassName s pairing unions powers separation collection carrier order hT valid Rf w).val.val
    stageOneRawSingle M data idx u.val.val w.val.val (s.encode p) ↔
      stageOneRawForces M (data 7) (data 8) (s.encode p) refinementActivityFormula ![u.val.val, w.val.val, U.val.val] ∧
      stageOneRawProfile M (data 7) (data 8) (s.encode p) (data 10) (data 11) (data 13) (b.encode E) bu aw ∧
      stageOneRawCompatibility M (data 7) (data 8) (s.encode p) (data 13) (data 12) (b.encode C) idx bu aw := by
  let data := M.refinementLevelFormulaData a s b d level T T2 valid
  let idx := refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
  let bu := M.stageOneClassName s pairing unions powers separation collection carrier order hT valid Rc u
  let aw := M.stageOneClassName s pairing unions powers separation collection carrier order hT valid Rf w
  have fields := M.refinementLevelFormulaData_fields s valid a b d level indices C E U Rf Rc member
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

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing.TransitiveGround
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
variable (level : ZFSet.{u})
variable {T2 : ZFSet.{u}} {valid2 : ∀ z ∈ T2, IsName s z}
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid)

include pairing unions powers separation collection carrier order

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

variable (indices : NiceRefinementIndexSystem M a s b d level T T2 valid valid2)

include indices in
theorem refinementLevelRawCompatibility_iff (C E : L) (U Rf Rc bu aw : (M.nameDomain s).names) (p : P)
    (member : refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
      M.niceRefinementIndices a s b d level T T2 valid) :
    let data := M.refinementLevelFormulaData a s b d level T T2 valid
    let idx := refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
    stageOneRawCompatibility M (data 7) (data 8) (s.encode p) (data 13) (data 12)
      (b.encode C) idx bu.val.val aw.val.val ↔
      Forces (M.nameDomain s) refinementCompatibilityFormula
        ![aw, M.stageOneVisibilityName s valid a b d base directed system C, bu,
          M.stageOneMapName s pairing unions powers separation collection carrier order hT valid U Rf Rc] p := by
  change stageOneRawCompatibility M s.carrier s.conditionOrder (s.encode p)
    (M.refinementLevelFormulaData a s b d level T T2 valid 13) (M.refinementLevelFormulaData a s b d level T T2 valid 12)
    (b.encode C) (refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val)
    bu.val.val aw.val.val ↔ _
  constructor
  · rintro ⟨V, hV, D, hD, visible, mapped, forced⟩
    have equalV := (M.refinementLevelFormulaData_visibility s valid a b d level (T2 := T2) base directed system C V).1 visible
    have equalD := (M.refinementLevelFormulaData_map s pairing unions powers separation collection carrier order
      hT valid a b d level indices C E U Rf Rc member D).1 mapped
    subst V
    subst D
    exact (raw_four M s pairing unions powers separation collection carrier order
      refinementCompatibilityFormula p aw (M.stageOneVisibilityName s valid a b d base directed system C) bu
      (M.stageOneMapName s pairing unions powers separation collection carrier order hT valid U Rf Rc)).1 forced
  · intro forced
    let V := M.stageOneVisibilityName s valid a b d base directed system C
    let D := M.stageOneMapName s pairing unions powers separation collection carrier order hT valid U Rf Rc
    refine ⟨V.val.val, V.property, D.val.val, D.property, ?_, ?_, ?_⟩
    · exact (M.refinementLevelFormulaData_visibility s valid a b d level (T2 := T2) base directed system C V.val.val).2 rfl
    · exact (M.refinementLevelFormulaData_map s pairing unions powers separation collection carrier order
        hT valid a b d level indices C E U Rf Rc member D.val.val).2 rfl
    · exact (raw_four M s pairing unions powers separation collection carrier order
        refinementCompatibilityFormula p aw V bu D).2 forced

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
