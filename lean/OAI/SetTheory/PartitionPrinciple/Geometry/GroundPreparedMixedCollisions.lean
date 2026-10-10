import OAI.SetTheory.PartitionPrinciple.Forcing.GroundNiceRefinementIndexActionLaws
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundPreparedCertificateActionPackages

namespace OAI

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L)
variable (d : PosetAction G L) (base : L)
variable (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
variable (system : NiceNameSystem M a s b d base directed T valid)
variable (H : ConditionFilter P)
variable (generic : H.GenericFor (formulaFamily (M.nameDomain s)))
variable (meet : L → L → L)
variable (descent : ∀ (v w : L) (x y : (M.nameDomain s).names),
  d.principalFix v ≤ a.stabilizer s x.val →
  d.principalFix w ≤ a.stabilizer s y.val →
  HereditarilySymmetric a s (d.principalSupportFamily base directed) x.val →
  HereditarilySymmetric a s (d.principalSupportFamily base directed) y.val →
  Name.eval {p | H.mem p} x.val = Name.eval {p | H.mem p} y.val →
  ∃ τ : (M.nameDomain s).names,
    HereditarilySymmetric a s (d.principalSupportFamily base directed) τ.val ∧
    d.principalFix (meet v w) ≤ a.stabilizer s τ.val ∧
    Name.eval {p | H.mem p} τ.val = Name.eval {p | H.mem p} x.val)

include system generic descent in
theorem common_value_visible (A B : L) (x y : (M.nameDomain s).names)
    (sx : d.principalFix A ≤ a.stabilizer s x.val)
    (sy : d.principalFix B ≤ a.stabilizer s y.val)
    (hx : HereditarilySymmetric a s (d.principalSupportFamily base directed) x.val)
    (hy : HereditarilySymmetric a s (d.principalSupportFamily base directed) y.val)
    (subset : Name.eval {p | H.mem p} x.val ⊆
      Name.eval {p | H.mem p} (Name.familySet ⊤ T valid))
    (values : Name.eval {p | H.mem p} x.val = Name.eval {p | H.mem p} y.val) :
    Name.eval {p | H.mem p} x.val ∈
      Name.eval {p | H.mem p} (M.niceVisibilityName a s T (d.principalFix (meet A B))) := by
  obtain ⟨τ, _, support, equal⟩ := descent A B x y sx sy hx hy values
  have bounded : Name.eval {p | H.mem p} τ.val ⊆
      Name.eval {p | H.mem p} (Name.familySet ⊤ T valid) := equal.symm ▸ subset
  exact equal ▸ system.normalization_visible (meet A B) τ support H generic bounded

include generic descent in
theorem mixed_collision_visible_both (A B : L)
    (x y : Fin 2 → (M.nameDomain s).names)
    (sx : ∀ i, d.principalFix A ≤ a.stabilizer s (x i).val)
    (sy : ∀ i, d.principalFix B ≤ a.stabilizer s (y i).val)
    (hx : ∀ i, HereditarilySymmetric a s (d.principalSupportFamily base directed) (x i).val)
    (hy : ∀ i, HereditarilySymmetric a s (d.principalSupportFamily base directed) (y i).val)
    (subset : ∀ i, Name.eval {p | H.mem p} (x i).val ⊆
      Name.eval {p | H.mem p} (Name.familySet ⊤ T valid))
    (q : P) (hq : H.mem q)
    (profile : Forces (M.nameDomain s) refinementProfileFormula
      ![x 0, x 1, M.stageOneVisibilityName s valid a b d base directed system (meet A B)] q)
    (collision : Name.eval {p | H.mem p} (x 0).val = Name.eval {p | H.mem p} (y 0).val ∨
      Name.eval {p | H.mem p} (x 1).val = Name.eval {p | H.mem p} (y 1).val) :
    ∀ i, Name.eval {p | H.mem p} (x i).val ∈
      Name.eval {p | H.mem p} (M.niceVisibilityName a s T (d.principalFix (meet A B))) := by
  let env : Assignment (M.nameDomain s) 3 :=
    ![x 0, x 1, M.stageOneVisibilityName s valid a b d base directed system (meet A B)]
  let N : TransitiveGround.{u} := ⟨(M.nameDomain s).values {p | H.mem p},
    (M.nameDomain s).values_transitive _⟩
  have realized := forces_sound (M.nameDomain s) H generic refinementProfileFormula env hq profile
  have paired := (N.realize_refinementProfileFormula (evalAssignment {p | H.mem p} env)
    (fun i => ⟨env i, rfl⟩)).1 realized
  change (Name.eval {p | H.mem p} (x 0).val ∈
      Name.eval {p | H.mem p} (M.niceVisibilityName a s T (d.principalFix (meet A B)))) ↔
    (Name.eval {p | H.mem p} (x 1).val ∈
      Name.eval {p | H.mem p} (M.niceVisibilityName a s T (d.principalFix (meet A B)))) at paired
  have one (i : Fin 2)
      (equal : Name.eval {p | H.mem p} (x i).val = Name.eval {p | H.mem p} (y i).val) :=
    M.common_value_visible a s b d base directed T valid system H generic meet descent
      A B (x i) (y i) (sx i) (sy i) (hx i) (hy i) (subset i) equal
  rcases collision with left | right
  · have first := one 0 left
    exact Fin.cases first (Fin.cases (paired.1 first) (fun i => Fin.elim0 i))
  · have second := one 1 right
    exact Fin.cases (paired.2 second) (Fin.cases second (fun i => Fin.elim0 i))

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {L G P : Type u}
variable [Group G] [PartialOrder L] [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
variable (nodes : b.carrier ∈ M.sets)
variable (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (maps : a.conditionMapFamily s t ∈ M.sets)
variable {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
variable (closed : ∀ g (tau : Name s), tau.val ∈ T → (a.act s g tau).val ∈ T)
include pairing unions powers separation collection carrier group nodes supports maps hT valid closed

theorem preparedValue_eval_agreement (F B f : ZFSet.{u})
    (z : (M.nameDomain s).names) (p q : P)
    (profile : F ⊆ b.carrier) (basis : B ⊆ F)
    (coinitial : ∀ x ∈ F, ∃ v ∈ B, ZFSet.pair v x ∈ b.conditionOrder)
    (function : ZFSet.IsFunc B (M.niceSupportNameCodes a s T d.principalFix) f)
    (supported : f ⊆ M.niceSupportRelation a s b T d.principalFix)
    (decisions : M.DecidesVisibilityProfile a s b d.principalFix T F z.val p)
    (equalities : ∀ v ∈ B, ∀ tau : Name s,
      tau.val ∈ M.niceSupportNameCodes a s T d.principalFix →
      ZFSet.pair v tau.val ∈ f → Name.ForcesEq p z.val tau)
    (g h : G) (V : L) (relative : g⁻¹ * h ∈ d.principalFix V)
    (qh : q ≤ a.iso h p) (qg : q ≤ a.iso g p)
    (H : ConditionFilter P) (generic : H.GenericFor (formulaFamily (M.nameDomain s)))
    (hq : H.mem q)
    (visible : Name.eval {r | H.mem r} (a.act s h z.val) ∈
      Name.eval {r | H.mem r} (M.niceVisibilityName a s T (d.principalFix (d.iso h V)))) :
    Name.eval {r | H.mem r} (a.act s h z.val) =
      Name.eval {r | H.mem r} (a.act s g z.val) := by
  have moved := M.decidesVisibilityProfile_act a s t b d pairing unions powers separation
    collection carrier maps closed F z.val p h decisions
  have hz := M.act_mem s a t pairing unions powers separation collection carrier maps h z.val z.property
  have hVisibility := M.niceVisibilityName_mem a s t b d.principalFix pairing unions powers
    separation collection carrier group supports maps hT valid (d.iso h V)
    (M.transitive nodes (b.encode_mem _))
  have member : b.encode V ∈ F := by
    by_contra absent
    have absentImage : b.encode (d.iso h V) ∉
        relationImage F b.carrier (b.graph b (d.iso h)) :=
      fun yes => absent ((visibilityProfileImage_entry b d F h V).1 yes)
    let traveled : (M.nameDomain s).names := ⟨a.act s h z.val, hz⟩
    let vis : (M.nameDomain s).names := ⟨M.niceVisibilityName a s T
      (d.principalFix (d.iso h V)), hVisibility⟩
    have negative : Forces (M.nameDomain s) (.neg (.mem 0 1) : SetFormula 2)
        ![traveled, vis] (a.iso h p) := (moved (d.iso h V)).2 absentImage
    exact (forces_sound (M.nameDomain s) H generic (.neg (.mem 0 1) : SetFormula 2)
      ![traveled, vis] (H.upward hq qh) negative) visible
  obtain ⟨raw, inBasis, lower⟩ := coinitial (b.encode V) member
  obtain ⟨v, rfl⟩ := (b.mem_carrier raw).1 (profile (basis inBasis))
  obtain ⟨code, entry, _⟩ := function.2 (b.encode v) inBasis
  have inCodes := (ZFSet.pair_mem_prod.1 (function.1 entry)).2
  let tau : Name s := ⟨code, M.niceSupportNameCodes_valid a s T d.principalFix code inCodes⟩
  have certificate := (M.pair_mem_niceSupportRelation a s b T d.principalFix v code).1
    (supported entry)
  have fixed : d.principalFix V ≤ a.stabilizer s tau :=
    le_trans (d.principalFix_antitone ((b.pair_mem_conditionOrder v V).1 lower))
      ((niceNameCode_iff a s tau).1 certificate.2).2
  have same : a.act s h tau = a.act s g tau := by
    have fixedName := fixed relative
    change a.act s (g⁻¹ * h) tau = tau at fixedName
    have translated := congrArg (a.act s g) fixedName
    rw [a.act_mul, a.act_inv_right] at translated
    exact translated
  have equality := equalities (b.encode v) inBasis tau inCodes entry
  have atoms : H.GenericFor (Name.atomicFamily (M.nameDomain s)) :=
    fun E hE dense => generic E (Or.inl hE) dense
  have hTau := M.act_mem s a t pairing unions powers separation collection carrier maps h tau certificate.1
  have gTau := M.act_mem s a t pairing unions powers separation collection carrier maps g tau certificate.1
  have gz := M.act_mem s a t pairing unions powers separation collection carrier maps g z.val z.property
  have first := Name.forcesEq_sound (M.nameDomain s) H atoms _ hz _ hTau q hq
    (Name.forcesEq_mono (a.forcesEq_act s h equality) qh)
  have second := Name.forcesEq_sound (M.nameDomain s) H atoms _ gz _ gTau q hq
    (Name.forcesEq_mono (a.forcesEq_act s g equality) qg)
  exact first.trans ((congrArg (Name.eval {r | H.mem r}) same).trans second.symm)

theorem preparedValue_forces_agreement (small : M.sets.Countable)
    (F B f : ZFSet.{u}) (z : (M.nameDomain s).names) (p q : P)
    (profile : F ⊆ b.carrier) (basis : B ⊆ F)
    (coinitial : ∀ x ∈ F, ∃ v ∈ B, ZFSet.pair v x ∈ b.conditionOrder)
    (function : ZFSet.IsFunc B (M.niceSupportNameCodes a s T d.principalFix) f)
    (supported : f ⊆ M.niceSupportRelation a s b T d.principalFix)
    (decisions : M.DecidesVisibilityProfile a s b d.principalFix T F z.val p)
    (equalities : ∀ v ∈ B, ∀ tau : Name s,
      tau.val ∈ M.niceSupportNameCodes a s T d.principalFix →
      ZFSet.pair v tau.val ∈ f → Name.ForcesEq p z.val tau)
    (g h : G) (V : L) (relative : g⁻¹ * h ∈ d.principalFix V)
    (qh : q ≤ a.iso h p) (qg : q ≤ a.iso g p) :
    let traveled (k : G) : (M.nameDomain s).names := ⟨a.act s k z.val,
      M.act_mem s a t pairing unions powers separation collection carrier maps k z.val z.property⟩
    let vis : (M.nameDomain s).names := ⟨M.niceVisibilityName a s T (d.principalFix (d.iso h V)),
      M.niceVisibilityName_mem a s t b d.principalFix pairing unions powers separation collection
        carrier group supports maps hT valid (d.iso h V) (M.transitive nodes (b.encode_mem _))⟩
    Forces (M.nameDomain s) (imp (.mem 0 1) (.equal 0 2)) ![traveled h, vis, traveled g] q := by
  dsimp only
  apply (M.ordinaryForces_iff_all_generics s small carrier _ _ q).2
  intro H hq generic
  apply (realize_imp _ _ _ _).2
  exact M.preparedValue_eval_agreement a s t b d pairing unions powers separation collection
    carrier group nodes supports maps hT valid closed F B f z p q profile basis coinitial function
    supported decisions equalities g h V relative qh qg H generic hq

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {L G P : Type u}
variable [Group G] [PartialOrder L] [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
variable (nodes : b.carrier ∈ M.sets)
variable (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (maps : a.conditionMapFamily s t ∈ M.sets)
variable {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
variable (closed : ∀ g (tau : Name s), tau.val ∈ T → (a.act s g tau).val ∈ T)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid)
variable (meet : L → L → L)
variable (descent : ∀ (H : ConditionFilter P),
  H.GenericFor (M.codedFamily s) →
  H.GenericFor (formulaFamily (M.nameDomain s)) →
  ∀ (v w : L) (x y : (M.nameDomain s).names),
    d.principalFix v ≤ a.stabilizer s x.val →
    d.principalFix w ≤ a.stabilizer s y.val →
    HereditarilySymmetric a s (d.principalSupportFamily base directed) x.val →
    HereditarilySymmetric a s (d.principalSupportFamily base directed) y.val →
    Name.eval {p | H.mem p} x.val = Name.eval {p | H.mem p} y.val →
    ∃ tau : (M.nameDomain s).names,
      HereditarilySymmetric a s (d.principalSupportFamily base directed) tau.val ∧
      d.principalFix (meet v w) ≤ a.stabilizer s tau.val ∧
      Name.eval {p | H.mem p} tau.val = Name.eval {p | H.mem p} x.val)

include group nodes supports hT closed descent in
theorem prepared_joint_mixed_collision_forces (small : M.sets.Countable)
    (F B f : Fin 2 → ZFSet.{u}) (z y : Fin 2 → (M.nameDomain s).names) (p q : P)
    (profiles : ∀ i, F i ⊆ b.carrier) (bases : ∀ i, B i ⊆ F i)
    (coinitial : ∀ i, ∀ x ∈ F i, ∃ v ∈ B i, ZFSet.pair v x ∈ b.conditionOrder)
    (functions : ∀ i, ZFSet.IsFunc (B i) (M.niceSupportNameCodes a s T d.principalFix) (f i))
    (supported : ∀ i, f i ⊆ M.niceSupportRelation a s b T d.principalFix)
    (decisions : ∀ i, M.DecidesVisibilityProfile a s b d.principalFix T (F i) (z i).val p)
    (equalities : ∀ i, ∀ v ∈ B i, ∀ tau : Name s,
      tau.val ∈ M.niceSupportNameCodes a s T d.principalFix →
      ZFSet.pair v tau.val ∈ f i → Name.ForcesEq p (z i).val tau)
    (g h : G) (V A X : L) (relative : g⁻¹ * h ∈ d.principalFix V)
    (qh : q ≤ a.iso h p) (qg : q ≤ a.iso g p) (overlap : meet A X = d.iso h V) :
    let moved := M.stageOneNameAction a s t pairing unions powers separation collection carrier maps
    ∀ (_newSupport : ∀ i, d.principalFix A ≤ a.stabilizer s (moved h (z i)).val)
      (_oldSupport : ∀ i, d.principalFix X ≤ a.stabilizer s (y i).val)
      (_newHS : ∀ i, HereditarilySymmetric a s (d.principalSupportFamily base directed)
        (moved h (z i)).val)
      (_oldHS : ∀ i, HereditarilySymmetric a s (d.principalSupportFamily base directed) (y i).val)
      (_shape : ∀ i, (moved h (z i)).val.val ⊆ ZFSet.prod T s.carrier)
      (_profileTest : Forces (M.nameDomain s) refinementProfileFormula
        ![moved h (z 0), moved h (z 1),
          M.stageOneVisibilityName s valid a b d base directed system (d.iso h V)] q)
      (_referenceTest : Forces (M.nameDomain s) refinementCollisionFormula
        ![moved g (z 0), y 0, moved g (z 1), y 1] q),
      Forces (M.nameDomain s) refinementCollisionFormula
        ![moved h (z 0), y 0, moved h (z 1), y 1] q := by
  let moved := M.stageOneNameAction a s t pairing unions powers separation collection carrier maps
  dsimp only
  intro newSupport oldSupport newHS oldHS shape profileTest referenceTest
  let env : Assignment (M.nameDomain s) 4 := ![moved h (z 0), y 0, moved h (z 1), y 1]
  let reference : Assignment (M.nameDomain s) 4 := ![moved g (z 0), y 0, moved g (z 1), y 1]
  apply (M.ordinaryForces_iff_all_joint_generics s small carrier refinementCollisionFormula env q).2
  intro H hq coded generic
  let N : TransitiveGround.{u} := ⟨(M.nameDomain s).values {r | H.mem r},
    (M.nameDomain s).values_transitive _⟩
  have old := (N.realize_refinementCollisionFormula (evalAssignment {r | H.mem r} reference)
    (fun i => ⟨reference i, rfl⟩)).1
    (forces_sound (M.nameDomain s) H generic refinementCollisionFormula reference hq referenceTest)
  change (Name.eval {r | H.mem r} (moved g (z 0)).val = Name.eval {r | H.mem r} (y 0).val ↔
    Name.eval {r | H.mem r} (moved g (z 1)).val = Name.eval {r | H.mem r} (y 1).val) at old
  have agreement
      (collision : Name.eval {r | H.mem r} (moved h (z 0)).val = Name.eval {r | H.mem r} (y 0).val ∨
        Name.eval {r | H.mem r} (moved h (z 1)).val = Name.eval {r | H.mem r} (y 1).val) :
      ∀ i, Name.eval {r | H.mem r} (moved h (z i)).val =
        Name.eval {r | H.mem r} (moved g (z i)).val := by
    have bounded (i : Fin 2) := Name.eval_subset_familySet_of_code_subset H T valid
      (moved h (z i)).val (shape i)
    have overlapProfile : Forces (M.nameDomain s) refinementProfileFormula
        ![moved h (z 0), moved h (z 1),
          M.stageOneVisibilityName s valid a b d base directed system (meet A X)] q :=
      overlap.symm ▸ profileTest
    have visible := M.mixed_collision_visible_both a s b d base directed T valid system H generic
      meet (descent H coded generic) A X (fun i => moved h (z i)) y newSupport oldSupport newHS oldHS
      bounded q hq overlapProfile collision
    intro i
    have atOverlap : Name.eval {r | H.mem r} (a.act s h (z i).val) ∈
        Name.eval {r | H.mem r} (M.niceVisibilityName a s T (d.principalFix (d.iso h V))) :=
      overlap ▸ visible i
    exact M.preparedValue_eval_agreement a s t b d pairing unions powers separation collection
      carrier group nodes supports maps hT valid closed (F i) (B i) (f i) (z i) p q (profiles i)
      (bases i) (coinitial i) (functions i) (supported i) (decisions i) (equalities i)
      g h V relative qh qg H generic hq atOverlap
  apply (N.realize_refinementCollisionFormula (evalAssignment {r | H.mem r} env)
    (fun i => ⟨env i, rfl⟩)).2
  change (Name.eval {r | H.mem r} (moved h (z 0)).val = Name.eval {r | H.mem r} (y 0).val ↔
    Name.eval {r | H.mem r} (moved h (z 1)).val = Name.eval {r | H.mem r} (y 1).val)
  constructor
  · intro first
    have equal := agreement (Or.inl first)
    exact (equal 1).trans (old.1 ((equal 0).symm.trans first))
  · intro second
    have equal := agreement (Or.inr second)
    exact (equal 0).trans (old.2 ((equal 1).symm.trans second))

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {L G P : Type u}
variable [Group G] [PartialOrder L] [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
variable (nodes : b.carrier ∈ M.sets)
variable (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (maps : a.conditionMapFamily s t ∈ M.sets)
variable {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
variable (closed : ∀ g (tau : Name s), tau.val ∈ T → (a.act s g tau).val ∈ T)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid)
variable (meet : L → L → L)
variable (descent : ∀ (H : ConditionFilter P),
  H.GenericFor (formulaFamily (M.nameDomain s)) →
  ∀ (v w : L) (x y : (M.nameDomain s).names),
    d.principalFix v ≤ a.stabilizer s x.val →
    d.principalFix w ≤ a.stabilizer s y.val →
    HereditarilySymmetric a s (d.principalSupportFamily base directed) x.val →
    HereditarilySymmetric a s (d.principalSupportFamily base directed) y.val →
    Name.eval {p | H.mem p} x.val = Name.eval {p | H.mem p} y.val →
    ∃ tau : (M.nameDomain s).names,
      HereditarilySymmetric a s (d.principalSupportFamily base directed) tau.val ∧
      d.principalFix (meet v w) ≤ a.stabilizer s tau.val ∧
      Name.eval {p | H.mem p} tau.val = Name.eval {p | H.mem p} x.val)

include group nodes supports hT closed descent in
theorem prepared_mixed_collision_forces (small : M.sets.Countable)
    (F B f : Fin 2 → ZFSet.{u}) (z y : Fin 2 → (M.nameDomain s).names) (p q : P)
    (profiles : ∀ i, F i ⊆ b.carrier) (bases : ∀ i, B i ⊆ F i)
    (coinitial : ∀ i, ∀ x ∈ F i, ∃ v ∈ B i, ZFSet.pair v x ∈ b.conditionOrder)
    (functions : ∀ i, ZFSet.IsFunc (B i) (M.niceSupportNameCodes a s T d.principalFix) (f i))
    (supported : ∀ i, f i ⊆ M.niceSupportRelation a s b T d.principalFix)
    (decisions : ∀ i, M.DecidesVisibilityProfile a s b d.principalFix T (F i) (z i).val p)
    (equalities : ∀ i, ∀ v ∈ B i, ∀ tau : Name s,
      tau.val ∈ M.niceSupportNameCodes a s T d.principalFix →
      ZFSet.pair v tau.val ∈ f i → Name.ForcesEq p (z i).val tau)
    (g h : G) (V A X : L) (relative : g⁻¹ * h ∈ d.principalFix V)
    (qh : q ≤ a.iso h p) (qg : q ≤ a.iso g p) (overlap : meet A X = d.iso h V) :
    let moved := M.stageOneNameAction a s t pairing unions powers separation collection carrier maps
    ∀ (_newSupport : ∀ i, d.principalFix A ≤ a.stabilizer s (moved h (z i)).val)
      (_oldSupport : ∀ i, d.principalFix X ≤ a.stabilizer s (y i).val)
      (_newHS : ∀ i, HereditarilySymmetric a s (d.principalSupportFamily base directed)
        (moved h (z i)).val)
      (_oldHS : ∀ i, HereditarilySymmetric a s (d.principalSupportFamily base directed) (y i).val)
      (_shape : ∀ i, (moved h (z i)).val.val ⊆ ZFSet.prod T s.carrier)
      (_profileTest : Forces (M.nameDomain s) refinementProfileFormula
        ![moved h (z 0), moved h (z 1),
          M.stageOneVisibilityName s valid a b d base directed system (d.iso h V)] q)
      (_referenceTest : Forces (M.nameDomain s) refinementCollisionFormula
        ![moved g (z 0), y 0, moved g (z 1), y 1] q),
      Forces (M.nameDomain s) refinementCollisionFormula
        ![moved h (z 0), y 0, moved h (z 1), y 1] q := by
  let moved := M.stageOneNameAction a s t pairing unions powers separation collection carrier maps
  dsimp only
  intro newSupport oldSupport newHS oldHS shape profileTest referenceTest
  let env : Assignment (M.nameDomain s) 4 := ![moved h (z 0), y 0, moved h (z 1), y 1]
  let reference : Assignment (M.nameDomain s) 4 := ![moved g (z 0), y 0, moved g (z 1), y 1]
  apply (M.ordinaryForces_iff_all_generics s small carrier refinementCollisionFormula env q).2
  intro H hq generic
  let N : TransitiveGround.{u} := ⟨(M.nameDomain s).values {r | H.mem r},
    (M.nameDomain s).values_transitive _⟩
  have old := (N.realize_refinementCollisionFormula (evalAssignment {r | H.mem r} reference)
    (fun i => ⟨reference i, rfl⟩)).1
    (forces_sound (M.nameDomain s) H generic refinementCollisionFormula reference hq referenceTest)
  change (Name.eval {r | H.mem r} (moved g (z 0)).val = Name.eval {r | H.mem r} (y 0).val ↔
    Name.eval {r | H.mem r} (moved g (z 1)).val = Name.eval {r | H.mem r} (y 1).val) at old
  have agreement
      (collision : Name.eval {r | H.mem r} (moved h (z 0)).val = Name.eval {r | H.mem r} (y 0).val ∨
        Name.eval {r | H.mem r} (moved h (z 1)).val = Name.eval {r | H.mem r} (y 1).val) :
      ∀ i, Name.eval {r | H.mem r} (moved h (z i)).val =
        Name.eval {r | H.mem r} (moved g (z i)).val := by
    have bounded (i : Fin 2) := Name.eval_subset_familySet_of_code_subset H T valid
      (moved h (z i)).val (shape i)
    have overlapProfile : Forces (M.nameDomain s) refinementProfileFormula
        ![moved h (z 0), moved h (z 1),
          M.stageOneVisibilityName s valid a b d base directed system (meet A X)] q :=
      overlap.symm ▸ profileTest
    have visible := M.mixed_collision_visible_both a s b d base directed T valid system H generic
      meet (descent H generic) A X (fun i => moved h (z i)) y newSupport oldSupport newHS oldHS
      bounded q hq overlapProfile collision
    intro i
    have atOverlap : Name.eval {r | H.mem r} (a.act s h (z i).val) ∈
        Name.eval {r | H.mem r} (M.niceVisibilityName a s T (d.principalFix (d.iso h V))) :=
      overlap ▸ visible i
    exact M.preparedValue_eval_agreement a s t b d pairing unions powers separation collection
      carrier group nodes supports maps hT valid closed (F i) (B i) (f i) (z i) p q (profiles i)
      (bases i) (coinitial i) (functions i) (supported i) (decisions i) (equalities i)
      g h V relative qh qg H generic hq atOverlap
  apply (N.realize_refinementCollisionFormula (evalAssignment {r | H.mem r} env)
    (fun i => ⟨env i, rfl⟩)).2
  change (Name.eval {r | H.mem r} (moved h (z 0)).val = Name.eval {r | H.mem r} (y 0).val ↔
    Name.eval {r | H.mem r} (moved h (z 1)).val = Name.eval {r | H.mem r} (y 1).val)
  constructor
  · intro first
    have equal := agreement (Or.inl first)
    exact (equal 1).trans (old.1 ((equal 0).symm.trans first))
  · intro second
    have equal := agreement (Or.inr second)
    exact (equal 0).trans (old.2 ((equal 1).symm.trans second))

end PartitionPilot.Forcing.TransitiveGround

end OAI
