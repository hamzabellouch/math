import OAI.SetTheory.PartitionPrinciple.Geometry.GroundNiceRefinementVisibility

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (level T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
variable (valid2 : ∀ z ∈ T2, IsName s z)
variable (indices : NiceRefinementIndexSystem M a s b d level T T2 valid valid2)

include indices in
theorem niceRefinementClasses_supported_by_block
    (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
    (closed : ∀ g (tau : Name s), tau.val ∈ T → (a.act s g tau).val ∈ T)
    (children : ∀ tau : Name s, tau.val ∈ T →
      HereditarilySymmetric a s (d.principalSupportFamily base directed) tau)
    (C E D : L) (U Rf Rc : (M.nameDomain s).names)
    (member : refinementIndexCode level (b.encode C) (b.encode E)
      U.val.val Rf.val.val Rc.val.val ∈ M.niceRefinementIndices a s b d level T T2 valid)
    (anchor : E ≤ D) (representatives : Fin 2 → Name s)
    (positions : ∀ i, d.principalFix D ≤ a.stabilizer s (representatives i)) :
    ∀ i, d.principalFix D ≤ a.stabilizer s
      (Name.refinementClass T valid (![Rc.val, Rf.val] i) (representatives i)) ∧
      HereditarilySymmetric a s (d.principalSupportFamily base directed)
        (Name.refinementClass T valid (![Rc.val, Rf.val] i) (representatives i)) := by
  obtain ⟨lower, _, fine, coarse, _⟩ := (indices.typed_entries C E U Rf Rc).1 member
  have atC := d.principalFix_antitone (le_trans (le_of_lt lower) anchor)
  have fineSupport := ((M.name_mem_niceNameCandidates a s T2 (d.principalFix C) Rf.val).1 fine).2.2
  have coarseSupport := ((M.name_mem_niceNameCandidates a s T2 (d.principalFix C) Rc.val).1 coarse).2.2
  have relation : ∀ i : Fin 2, d.principalFix D ≤ a.stabilizer s (![Rc.val, Rf.val] i) :=
    Fin.cases (atC.trans coarseSupport)
      (Fin.cases (atC.trans fineSupport) (fun j => Fin.elim0 j))
  intro i
  exact ⟨Name.refinementClass_support a T valid closed _ _ (d.principalFix D)
    (relation i) (positions i),
    Name.refinementClass_hs a (d.principalSupportFamily base directed) T valid closed children
      _ _ (d.principalFix D) ⟨D, le_rfl⟩ (relation i) (positions i)⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
