import OAI.SetTheory.PartitionPrinciple.Geometry.GroundMainFinalStructuralCompression

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable {T T2 : ZFSet.{u}} (hT : T ∈ M.sets)
variable (valid : ∀ z ∈ T, IsName s z) {valid2 : ∀ z ∈ T2, IsName s z}
variable (a : PosetAction G P) (t : Presentation G)
variable (maps : a.conditionMapFamily s t ∈ M.sets)
variable (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (terms : ∀ g (z : Name s), z.val ∈ T → (a.act s g z).val ∈ T)
variable (system : NiceNameSystem M a s b d base directed T valid)
variable (level : ZFSet.{u})
variable (indices : NiceRefinementIndexSystem M a s b d level T T2 valid valid2)

include indices terms in
theorem refinementAbsentLift_class_transport (small : M.sets.Countable)
    (C E D K : L) (U Rf Rc u : (M.nameDomain s).names)
    (member : refinementIndexCode level (b.encode C) (b.encode E)
      U.val.val Rf.val.val Rc.val.val ∈ M.niceRefinementIndices a s b d level T T2 valid)
    (term : u.val.val ∈ T) (above : C ≤ D)
    (support : d.principalFix D ≤ a.stabilizer s u.val)
    (g : G) (fixed : g ∈ d.principalFix C) (cap : d.iso g D ≤ K)
    (r q : P) (below : q ≤ a.iso g r) (active : Name.ForcesMem r u.val U.val) :
    let cls := M.stageOneClassName s pairing unions powers separation collection carrier order hT valid
    let vis := M.stageOneVisibilityName s valid a b d base directed system
    let w : (M.nameDomain s).names := ⟨a.act s g u.val,
      M.act_mem s a t pairing unions powers separation collection carrier maps g u.val u.property⟩
    (∀ p, p ≤ r → ¬ Name.ForcesMem p (cls Rf u).val (vis C).val) →
    w.val.val ∈ T ∧ Name.ForcesMem q w.val U.val ∧
    a.act s g (cls Rf u).val = (cls Rf w).val ∧
    d.principalFix K ≤ a.stabilizer s (cls Rf w).val ∧
    Name.ForcesMem q (cls Rf w).val (vis K).val ∧
    (∀ p, p ≤ q → ¬ Name.ForcesMem p (cls Rf w).val (vis C).val) := by
  dsimp only
  let cls := M.stageOneClassName s pairing unions powers separation collection carrier order hT valid
  let vis := M.stageOneVisibilityName s valid a b d base directed system
  let w : (M.nameDomain s).names := ⟨a.act s g u.val,
    M.act_mem s a t pairing unions powers separation collection carrier maps g u.val u.property⟩
  intro absent
  obtain ⟨_, domain, fine, _, _⟩ := (indices.typed_entries C E U Rf Rc).1 member
  have domainFixed : a.act s g U.val = U.val :=
    ((M.name_mem_niceNameCandidates a s T (d.principalFix C) U.val).1 domain).2.2 fixed
  have relationSupport :=
    ((M.name_mem_niceNameCandidates a s T2 (d.principalFix C) Rf.val).1 fine).2.2
  have relationFixed : a.act s g Rf.val = Rf.val := relationSupport fixed
  have classAction : a.act s g (cls Rf u).val = (cls Rf w).val := by
    change a.act s g (Name.refinementClass T valid Rf.val u.val) =
      Name.refinementClass T valid Rf.val (a.act s g u.val)
    rw [Name.act_refinementClass a T valid terms, relationFixed]
  have classSupport : d.principalFix D ≤ a.stabilizer s (cls Rf u).val :=
    Name.refinementClass_support a T valid terms Rf.val u.val (d.principalFix D)
      ((d.principalFix_antitone above).trans relationSupport) support
  have movedSupport : d.principalFix K ≤ a.stabilizer s (cls Rf w).val := by
    rw [← classAction]
    exact a.compressed_name_support s d g D K (cls Rf u).val classSupport cap
  have visible : Name.ForcesMem q (cls Rf w).val (vis K).val := by
    change Forces (M.nameDomain s) (.mem 0 1) ![cls Rf w, vis K] q
    apply (M.ordinaryForces_iff_all_generics s small carrier _ _ q).2
    intro H hq generic
    apply system.normalization_visible K (cls Rf w) movedSupport H generic
    change Name.eval {p | H.mem p} (Name.refinementClass T valid Rf.val w.val) ⊆ _
    rw [M.eval_refinementClass s pairing carrier hT valid Rf.val w.val
      Rf.property w.property H generic]
    exact equivalenceClass_subset _ _ _
  have activeW := a.forcesMem_act s g active
  rw [domainFixed] at activeW
  refine ⟨terms g u.val term, Name.forcesMem_mono activeW below,
    classAction, movedSupport, visible, ?_⟩
  have visibilityFixed : a.act s g (vis C).val = (vis C).val := system.visibility_support C fixed
  intro p pq bad
  have oldBelow : (a.iso g).symm p ≤ r := by
    simpa using (a.iso g).symm.monotone (pq.trans below)
  have moved : Name.ForcesMem (a.iso g ((a.iso g).symm p))
      (a.act s g (cls Rf u).val) (a.act s g (vis C).val) := by
    simpa only [OrderIso.apply_symm_apply, classAction, visibilityFixed] using bad
  exact absent _ oldBelow ((a.forcesMem_act_iff s g _ _ _).1 moved)

end PartitionPilot.Forcing.TransitiveGround

end OAI
