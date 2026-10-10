import Mathlib
import OAI.Topology.ArtinGroups.Realizations.CellInteriorChart

namespace OAI

namespace HarmonicArtin
open Topology Set Metric Geometric CoxeterExchange

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type*} [Fintype S] [DecidableEq S] (M : CoxeterMatrix S)

omit [Fintype S] [DecidableEq S] in
lemma sourceCellIndex_type_injective :
    Function.Injective (fun i : Σ n,SourceCellIndex M n => i.2.val) := by
  rintro ⟨n,⟨T,hT⟩⟩ ⟨m,⟨R,hR⟩⟩ he
  change T=R at he
  subst R
  cases hT
  cases hR
  rfl

noncomputable instance sourceCWComplex : CWComplex (Set.univ : Set (SourceSalvetti M)) where
  cell := SourceCellIndex M
  map _ i := sourceCellPartial M i
  source_eq _ i := sourceCellPartial_source M i
  continuousOn _ i := sourceCellTotal_continuousOn M i
  continuousOn_symm _ i := sourceCellPartial_continuousOn_symm M i
  pairwiseDisjoint' := by
    intro i _ j _ hij
    change Disjoint ((sourceCellPartial M i.2) '' ball 0 1) ((sourceCellPartial M j.2) '' ball 0 1)
    rw [sourceCellPartial_image_ball,sourceCellPartial_image_ball]
    exact sourceOpenCell_disjoint M (fun h => hij (sourceCellIndex_type_injective M h))
  mapsTo' := by
    intro n i
    refine ⟨fun m => Finset.univ,?_⟩
    intro x hx
    obtain ⟨m,hm,j,hj⟩ := sourceCellPartial_boundary M i x hx
    simp only [Set.mem_iUnion]
    exact ⟨m,hm,j,Finset.mem_univ j,hj⟩
  closed' := by
    intro A _ hA
    apply (sourceCharacteristic_weak M A).mpr
    intro T
    let i : SourceCellIndex M T.val.ncard := ⟨T,rfl⟩
    have h := (hA _ i).preimage (sourceCharacteristic M T).continuous
    rw [sourceCellPartial_image_closedBall] at h
    have hr : (sourceCharacteristic M T) ⁻¹' Set.range (sourceCharacteristic M T)=Set.univ :=
      Set.eq_univ_of_forall (fun x => ⟨x,rfl⟩)
    change IsClosed ((sourceCharacteristic M T) ⁻¹' (A ∩ Set.range (sourceCharacteristic M T))) at h
    simpa only [Set.preimage_inter,hr,Set.inter_univ] using h
  union' := by
    apply Set.eq_univ_of_forall
    intro q
    obtain ⟨T,x,hx⟩ := sourceOpenCell_cover M q
    refine Set.mem_iUnion.mpr ⟨T.val.ncard,Set.mem_iUnion.mpr ⟨⟨T,rfl⟩,?_⟩⟩
    rw [sourceCellPartial_image_closedBall]
    exact ⟨x.val,hx⟩

instance sourceCWFiniteType : CWComplex.FiniteType (Set.univ : Set (SourceSalvetti M)) where
  finite_cell n := inferInstanceAs (Finite (SourceCellIndex M n))

instance sourceCWFiniteDimensional : CWComplex.FiniteDimensional (Set.univ : Set (SourceSalvetti M)) where
  eventually_isEmpty_cell := by
    apply Filter.eventually_atTop.mpr
    refine ⟨Fintype.card S+1,fun n hn => ?_⟩
    change IsEmpty (SourceCellIndex M n)
    refine ⟨fun i => ?_⟩
    have hc : i.val.val.ncard ≤ Fintype.card S := by simpa only [Nat.card_eq_fintype_card] using Set.ncard_le_card i.val.val
    have hi := i.property
    omega

instance sourceCWFinite : CWComplex.Finite (Set.univ : Set (SourceSalvetti M)) :=
  CWComplex.finite_of_finiteDimensional_finiteType _

theorem sourceCW_openCell {n : ℕ} (i : SourceCellIndex M n) :
    CWComplex.openCell (C := (Set.univ : Set (SourceSalvetti M))) n i=sourceOpenCell M i.val :=
  sourceCellPartial_image_ball M i

end HarmonicArtin

end OAI
