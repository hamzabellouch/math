import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundMainStageFromCodes

namespace OAI

section

namespace PartitionPilot.Forcing

universe u

structure MeetEmbeddingCode (A L rA rL μA μL e : ZFSet.{u}) : Prop where
  injection : InjectionCode A L e
  monotone : ∀ x y x' y', ZFSet.pair x y ∈ rA →
    ZFSet.pair x x' ∈ e → ZFSet.pair y y' ∈ e → ZFSet.pair x' y' ∈ rL
  map_meet : ∀ x y z x' y' z', ZFSet.pair (ZFSet.pair x y) z ∈ μA →
    ZFSet.pair x x' ∈ e → ZFSet.pair y y' ∈ e → ZFSet.pair z z' ∈ e →
      ZFSet.pair (ZFSet.pair x' y') z' ∈ μL

theorem meetFilter_copyPullback {A L rA rL μA μL e F : ZFSet.{u}}
    (source : MeetOrderCode A rA μA) (target : MeetFilterCode L rL μL F)
    (embedding : MeetEmbeddingCode A L rA rL μA μL e)
    (nonempty : (copyPullback A L e F).Nonempty) :
    MeetFilterCode A rA μA (copyPullback A L e F) where
  subset := fun x hx => ((mem_copyPullback A L e F x).1 hx).1
  nonempty := nonempty
  upward := by
    intro x hx y hy lower
    obtain ⟨_, x', hxF, _, xx'⟩ := (mem_copyPullback A L e F x).1 hx
    obtain ⟨y', yy', _⟩ := embedding.injection.function.2 y hy
    have hyL := (ZFSet.pair_mem_prod.1 (embedding.injection.function.1 yy')).2
    have hyF := target.upward x' hxF y' hyL (embedding.monotone x y x' y' lower xx' yy')
    exact (mem_copyPullback A L e F y).2 ⟨hy, y', hyF, hyL, yy'⟩
  closed_meet := by
    intro x hx y hy z meetXY
    obtain ⟨_, x', hxF, _, xx'⟩ := (mem_copyPullback A L e F x).1 hx
    obtain ⟨_, y', hyF, _, yy'⟩ := (mem_copyPullback A L e F y).1 hy
    have hzA := (ZFSet.pair_mem_prod.1 (source.operation.1 meetXY)).2
    obtain ⟨z', zz', _⟩ := embedding.injection.function.2 z hzA
    have hzL := (ZFSet.pair_mem_prod.1 (embedding.injection.function.1 zz')).2
    have hzF := target.closed_meet x' hxF y' hyF z'
      (embedding.map_meet x y z x' y' z' meetXY xx' yy' zz')
    exact (mem_copyPullback A L e F z).2 ⟨hzA, z', hzF, hzL, zz'⟩

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem internalCountableBelow_copy_of_all_filters
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    {A L rA rL μA μL e F : ZFSet.{u}}
    (hA : A ∈ M.sets) (hL : L ∈ M.sets) (he : e ∈ M.sets) (hF : F ∈ M.sets)
    (source : MeetOrderCode A rA μA) (target : MeetFilterCode L rL μL F)
    (embedding : MeetEmbeddingCode A L rA rL μA μL e)
    (earlier : ∀ P ∈ M.sets, MeetFilterCode A rA μA P → M.InternalCountableBelow rA P P) :
    M.InternalCountableBelow rL F (F ∩ relationImage A L e) := by
  classical
  by_cases nonempty : (copyPullback A L e F).Nonempty
  · have pullbackMember := M.copyPullback_mem pairing unions powers separation hA hL he hF
    have pullbackFilter := meetFilter_copyPullback source target embedding nonempty
    exact M.internalCountableBelow_copy_pullback pairing unions powers separation infinite hL he
      embedding.injection embedding.monotone
      (earlier (copyPullback A L e F) pullbackMember pullbackFilter)
  · refine ⟨∅, M.empty_mem ⟨F, hF⟩, M.empty_groundEmbeddable ZFSet.omega ⟨F, hF⟩,
      ZFSet.empty_subset F, ?_⟩
    intro x hx
    obtain ⟨hxF, image⟩ := ZFSet.mem_inter.1 hx
    obtain ⟨hxL, y, hyA, yx⟩ := (mem_relationImage A L e x).1 image
    exact False.elim (nonempty ⟨y,
      (mem_copyPullback A L e F y).2 ⟨hyA, x, hxF, hxL, yx⟩⟩)

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
