import OAI.SetTheory.PartitionPrinciple.Forcing.GroundRenamedNameFamilyBounds
import OAI.SetTheory.PartitionPrinciple.Forcing.RefinementCoarseImageNames

namespace OAI

section

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

include pairing unions powers separation collection carrier order in
theorem refinementCoarseImage_mem {T : ZFSet.{u}} (hT : T ∈ M.sets)
    (valid : ∀ z ∈ T, IsName s z) (U sigma Rc : (M.nameDomain s).names) :
    (Name.refinementCoarseImage (M.nameDomain s) T valid U sigma Rc).val ∈ M.sets :=
  M.ordinarySeparationName_mem s pairing unions powers separation collection carrier order
    BoundedFormula.coarseClassImageFormula.toFormula (extend U (extend sigma (extend Rc Fin.elim0)))
    ⟨Name.familySet ⊤ T valid, M.familySet_mem s ⊤ pairing unions powers separation hT
      (M.transitive carrier (s.encode_mem ⊤)) valid⟩

variable (a : PosetAction G P) (t : Presentation G)
variable (maps : a.conditionMapFamily s t ∈ M.sets)
variable (b : Presentation L) (d : PosetAction G L) (base : L)
variable (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
variable (terms : ∀ g (z : Name s), z.val ∈ T → (a.act s g z).val ∈ T)

include pairing unions powers separation collection carrier maps terms in
theorem refinementCoarseImage_principal_support (U sigma Rc : (M.nameDomain s).names)
    {C v : L} (lower : C ≤ v)
    (domain : d.principalFix C ≤ a.stabilizer s U.val)
    (witness : d.principalFix v ≤ a.stabilizer s sigma.val)
    (relation : d.principalFix C ≤ a.stabilizer s Rc.val) :
    d.principalFix v ≤ a.stabilizer s (Name.refinementCoarseImage (M.nameDomain s) T valid U sigma Rc) :=
  Name.refinementCoarseImage_support a (M.nameDomain s)
    (fun g z hz => M.act_mem s a t pairing unions powers separation collection carrier maps g z hz)
    T valid terms U sigma Rc (d.principalFix v)
    (le_trans (d.principalFix_antitone lower) domain) witness
    (le_trans (d.principalFix_antitone lower) relation)

include pairing unions powers separation collection carrier order maps hT terms in
theorem coarseClass_visible_of_fineValue
    (system : NiceNameSystem M a s b d base directed T valid)
    (U sigma Rf Rc : (M.nameDomain s).names) {C v : L} (lower : C ≤ v)
    (domain : d.principalFix C ≤ a.stabilizer s U.val)
    (witness : d.principalFix v ≤ a.stabilizer s sigma.val)
    (relation : d.principalFix C ≤ a.stabilizer s Rc.val)
    (H : ConditionFilter P) (generic : H.GenericFor (formulaFamily (M.nameDomain s)))
    (validity : RefinementValidityCode (Name.eval {p | H.mem p} (Name.familySet ⊤ T valid))
      (Name.eval {p | H.mem p} U.val) (Name.eval {p | H.mem p} Rf.val) (Name.eval {p | H.mem p} Rc.val))
    {x : ZFSet.{u}} (hx : x ∈ Name.eval {p | H.mem p} U.val)
    (fineValue : Name.eval {p | H.mem p} sigma.val =
      equivalenceClass (Name.eval {p | H.mem p} U.val) (Name.eval {p | H.mem p} Rf.val) x) :
    equivalenceClass (Name.eval {p | H.mem p} U.val) (Name.eval {p | H.mem p} Rc.val) x ∈
      Name.eval {p | H.mem p} (M.niceVisibilityName a s T (d.principalFix v)) := by
  let image : (M.nameDomain s).names :=
    ⟨Name.refinementCoarseImage (M.nameDomain s) T valid U sigma Rc,
      M.refinementCoarseImage_mem s pairing unions powers separation collection carrier order hT valid U sigma Rc⟩
  have support := M.refinementCoarseImage_principal_support s pairing unions powers separation collection
    carrier a t maps d valid terms U sigma Rc lower domain witness relation
  have family := M.familySet_mem s ⊤ pairing unions powers separation hT
    (M.transitive carrier (s.encode_mem ⊤)) valid
  have value : Name.eval {p | H.mem p} image.val =
      equivalenceClass (Name.eval {p | H.mem p} U.val) (Name.eval {p | H.mem p} Rc.val) x := by
    change Name.eval {p | H.mem p} (Name.refinementCoarseImage (M.nameDomain s) T valid U sigma Rc) = _
    rw [Name.eval_refinementCoarseImage_of_subset (M.nameDomain s) T valid U sigma Rc family H generic validity.1,
      fineValue, coarseClassImage_of_fineClass validity.2.1 validity.2.2.1 validity.2.2.2 hx]
  have subset : Name.eval {p | H.mem p} image.val ⊆
      Name.eval {p | H.mem p} (Name.familySet ⊤ T valid) := by
    rw [value]
    exact fun _ h => validity.1 (equivalenceClass_subset _ _ _ h)
  exact value ▸ system.normalization_visible v image support H generic subset

include pairing unions powers separation collection carrier order maps hT terms in
theorem refinementQuotientMap_preserves_visibility
    (system : NiceNameSystem M a s b d base directed T valid)
    (U Rf Rc : (M.nameDomain s).names) {C v : L} (lower : C ≤ v)
    (domain : d.principalFix C ≤ a.stabilizer s U.val)
    (relation : d.principalFix C ≤ a.stabilizer s Rc.val)
    (H : ConditionFilter P) (generic : H.GenericFor (formulaFamily (M.nameDomain s)))
    (validity : RefinementValidityCode (Name.eval {p | H.mem p} (Name.familySet ⊤ T valid))
      (Name.eval {p | H.mem p} U.val) (Name.eval {p | H.mem p} Rf.val) (Name.eval {p | H.mem p} Rc.val))
    {fineClass coarseClass : ZFSet.{u}}
    (visible : fineClass ∈ Name.eval {p | H.mem p} (M.niceVisibilityName a s T (d.principalFix v)))
    (entry : ZFSet.pair fineClass coarseClass ∈ refinementQuotientMap
      (Name.eval {p | H.mem p} U.val) (Name.eval {p | H.mem p} Rf.val) (Name.eval {p | H.mem p} Rc.val)) :
    coarseClass ∈ Name.eval {p | H.mem p} (M.niceVisibilityName a s T (d.principalFix v)) := by
  obtain ⟨sigma, candidate, value⟩ :=
    (M.mem_eval_niceVisibilityName a s T (d.principalFix v) {p | H.mem p} H.top_mem fineClass).1 visible
  have hsigma := (M.name_mem_niceNameCandidates a s T (d.principalFix v) sigma).1 candidate
  obtain ⟨x, hx, fineValue, coarseValue⟩ := (pair_mem_refinementQuotientMap _ _ _ _ _).1 entry
  rw [coarseValue]
  exact M.coarseClass_visible_of_fineValue s pairing unions powers separation collection carrier order
    a t maps b d base directed hT valid terms system U ⟨sigma, hsigma.1⟩ Rf Rc lower domain hsigma.2.2
    relation H generic validity hx (value.trans fineValue)

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
