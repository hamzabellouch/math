import OAI.SetTheory.PartitionPrinciple.Geometry.GroundHeightPushforward
import OAI.SetTheory.PartitionPrinciple.Transfinite.OwnerBirthLayers

namespace OAI

namespace PartitionPilot.Forcing
open SetFormula
universe u

theorem MeetEmbeddingCode.compose {A B C rA rB rC μA μB μC e f : ZFSet.{u}}
    (first : MeetEmbeddingCode A B rA rB μA μB e)
    (second : MeetEmbeddingCode B C rB rC μB μC f) :
    MeetEmbeddingCode A C rA rC μA μC (relationCompose A B C e f) := by
  refine ⟨first.injection.compose second.injection, ?_, ?_⟩
  · intro x y x' y' lower xx yy
    obtain ⟨_, _, a, _, xa, ax⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 xx
    obtain ⟨_, _, b, _, yb, by'⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 yy
    exact second.monotone a b x' y' (first.monotone x y a b lower xa yb) ax by'
  · intro x y z x' y' z' meet xx yy zz
    obtain ⟨_, _, a, _, xa, ax⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 xx
    obtain ⟨_, _, b, _, yb, by'⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 yy
    obtain ⟨_, _, c, _, zc, cz⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 zz
    exact second.map_meet a b c x' y' z' (first.map_meet x y z a b c meet xa yb zc) ax by' cz

theorem relationImage_compose_point {A B C e f x y : ZFSet.{u}}
    (image : x ∈ relationImage A B e) (hy : y ∈ C) (entry : ZFSet.pair x y ∈ f) :
    y ∈ relationImage A C (relationCompose A B C e f) := by
  obtain ⟨hx, a, ha, copied⟩ := (mem_relationImage _ _ _ _).1 image
  exact (mem_relationImage _ _ _ _).2 ⟨hy, a, ha,
    (pair_mem_relationCompose _ _ _ _ _ _ _).2 ⟨ha, hy, x, hx, copied, entry⟩⟩

theorem OldBridgeCode.map {A B rA rB μA μB birthA birthB t x y x' y' e : ZFSet.{u}}
    (source : MeetOrderCode A rA μA) (embedding : MeetEmbeddingCode A B rA rB μA μB e)
    (preserves : ∀ a b s, ZFSet.pair a b ∈ e → ZFSet.pair a s ∈ birthA → ZFSet.pair b s ∈ birthB)
    (xx : ZFSet.pair x x' ∈ e) (yy : ZFSet.pair y y' ∈ e)
    (bridge : OldBridgeCode A rA μA birthA t x y) : OldBridgeCode B rB μB birthB t x' y' := by
  rcases bridge with ⟨z, s, meet, born, before⟩ | ⟨z, hz, s, born, before, between⟩
  · have hz := (ZFSet.pair_mem_prod.1 (source.operation.1 meet)).2
    obtain ⟨z', zz, _⟩ := embedding.injection.function.2 z hz
    exact Or.inl ⟨z', s, embedding.map_meet x y z x' y' z' meet xx yy zz,
      preserves z z' s zz born, before⟩
  · obtain ⟨z', zz, _⟩ := embedding.injection.function.2 z hz
    refine Or.inr ⟨z', (ZFSet.pair_mem_prod.1 (embedding.injection.function.1 zz)).2,
      s, preserves z z' s zz born, before, ?_⟩
    exact between.elim
      (fun h => Or.inl ⟨embedding.monotone x z x' z' h.1 xx zz, embedding.monotone z y z' y' h.2 zz yy⟩)
      (fun h => Or.inr ⟨embedding.monotone y z y' z' h.1 yy zz, embedding.monotone z x z' x' h.2 zz xx⟩)

noncomputable def CodedGrowthLayer.pushforward
    {M : TransitiveGround.{u}} {Space sourceOrder sourceMeet : ZFSet.{u} → ZFSet.{u}}
    {A B rA rB μA μB old born t e : ZFSet.{u}}
    (layer : CodedGrowthLayer M Space sourceOrder sourceMeet A rA μA old t)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hA : A ∈ M.sets) (hB : B ∈ M.sets) (he : e ∈ M.sets) (hOmega : ZFSet.omega ∈ M.sets)
    (groundSources : ∀ s ∈ t, Space s ∈ M.sets)
    (source : MeetOrderCode A rA μA) (embedding : MeetEmbeddingCode A B rA rB μA μB e)
    (preserves : ∀ x y a, ZFSet.pair x y ∈ e → (ZFSet.pair y a ∈ born ↔ ZFSet.pair x a ∈ old))
    (noNew : ∀ y ∈ B, ZFSet.pair y t ∈ born → ∃ x ∈ A, ZFSet.pair x y ∈ e) :
    CodedGrowthLayer M Space sourceOrder sourceMeet B rB μB born t := by
  classical
  cases layer with
  | countablePoints D ground small cover =>
    let retained := ZFSet.sep (fun x => x ∈ A) D
    have retainedGround : retained ∈ M.sets :=
      M.bounded_separation_mem separation (.mem 0 1) (extend A Fin.elim0)
        (Fin.cases hA (fun i => Fin.elim0 i)) ground
    have retainedSmall := M.groundEmbeddable_restrict separation retainedGround hOmega
      (fun _ h => (ZFSet.mem_sep.1 h).1) small
    refine .countablePoints (relationImage retained B e)
      (M.relationImage_mem separation retainedGround hB he)
      (M.groundEmbeddable_image pairing unions powers separation retainedGround hB hOmega he
        embedding.injection (fun _ h => (ZFSet.mem_sep.1 h).2) retainedSmall) ?_
    intro y hy yt
    obtain ⟨x, hx, xy⟩ := noNew y hy yt
    exact (mem_relationImage _ _ _ _).2 ⟨hy, x,
      ZFSet.mem_sep.2 ⟨cover x hx ((preserves x y t xy).1 yt), hx⟩, xy⟩
  | copies I parts groundI small groundParts index copy earlier groundCopy copyCode cover inCopy =>
    refine .copies I (relationCompose I A B parts e) groundI small
      (M.relationCompose_mem pairing unions powers separation groundI hA hB groundParts he)
      index (fun i => relationCompose (Space (index i)) A B (copy i) e) earlier
      (fun i hi => M.relationCompose_mem pairing unions powers separation
        (groundSources (index i) (earlier i hi)) hA hB (groundCopy i hi) he)
      (fun i hi => (copyCode i hi).compose embedding) ?_ ?_
    · intro y hy yt
      obtain ⟨x, hx, xy⟩ := noNew y hy yt
      obtain ⟨i, hi, part⟩ := cover x hx ((preserves x y t xy).1 yt)
      exact ⟨i, hi, (pair_mem_relationCompose _ _ _ _ _ _ _).2 ⟨hi, hy, x, hx, part, xy⟩⟩
    · intro i hi y hy part
      obtain ⟨_, _, x, hx, oldPart, xy⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 part
      exact relationImage_compose_point (inCopy i hi x hx oldPart) hy xy
  | separated I index copy earlier groundCopy copyCode component cover separated =>
    let pre (x : {x : ZFSet.{u} // x ∈ B ∧ ZFSet.pair x t ∈ born}) :
        {x : ZFSet.{u} // x ∈ A ∧ ZFSet.pair x t ∈ old} :=
      let a := Classical.choose (noNew x.val x.property.1 x.property.2)
      have spec := Classical.choose_spec (noNew x.val x.property.1 x.property.2)
      ⟨a, spec.1, (preserves a x.val t spec.2).1 x.property.2⟩
    have preEntry (x : {x : ZFSet.{u} // x ∈ B ∧ ZFSet.pair x t ∈ born}) :
        ZFSet.pair (pre x).val x.val ∈ e :=
      (Classical.choose_spec (noNew x.val x.property.1 x.property.2)).2
    refine .separated I index (fun i => relationCompose (Space (index i)) A B (copy i) e) earlier
      (fun i => M.relationCompose_mem pairing unions powers separation
        (groundSources (index i) (earlier i)) hA hB (groundCopy i) he)
      (fun i => (copyCode i).compose embedding) (fun x => component (pre x)) ?_ ?_
    · intro x
      exact relationImage_compose_point (cover (pre x)) x.property.1 (preEntry x)
    · intro x y different
      exact (separated (pre x) (pre y) different).map source embedding
        (fun a b s copied born => (preserves a b s copied).2 born) (preEntry x) (preEntry y)

noncomputable def CodedGrowthLayer.ownerBirth_pushforward
    {M : TransitiveGround.{u}} {Space sourceOrder sourceMeet : ZFSet.{u} → ZFSet.{u}}
    {A B L rA rL μA μL old T0 T levels stamps t e : ZFSet.{u}}
    (layer : CodedGrowthLayer M Space sourceOrder sourceMeet A rA μA old t)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hA : A ∈ M.sets) (hL : L ∈ M.sets) (he : e ∈ M.sets) (hOmega : ZFSet.omega ∈ M.sets)
    (groundSources : ∀ s ∈ t, Space s ∈ M.sets)
    (source : MeetOrderCode A rA μA) (embedding : MeetEmbeddingCode A L rA rL μA μL e)
    (carrier : L ⊆ B) (oldFunction : ZFSet.IsFunc A T0 old)
    (before : ∀ n a, ZFSet.pair (natSetCode n) a ∈ stamps → t ∈ a) :
    CodedGrowthLayer M Space sourceOrder sourceMeet L rL μL
      (ownerBirthGraph (relationImage A B e) B T (pushedHeightGraph A B T0 e old) levels stamps) t := by
  have injection : InjectionCode A B e := by
    refine ⟨⟨?_, embedding.injection.function.2⟩, embedding.injection.injective⟩
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 (embedding.injection.function.1 hz)
    exact ZFSet.pair_mem_prod.2 ⟨hx, carrier hy⟩
  have pushed := pushedHeightGraph_function injection oldFunction
  apply layer.pushforward pairing unions powers separation hA hL he hOmega groundSources source embedding
  · intro x y a copied
    have bounds := ZFSet.pair_mem_prod.1 (injection.function.1 copied)
    have oldPoint := (mem_relationImage A B e y).2 ⟨bounds.2, x, bounds.1, copied⟩
    rw [ownerBirthGraph_old_iff oldPoint, pushedHeightGraph_entry injection oldFunction copied]
  · intro y _ entry
    rcases (pair_mem_ownerBirthGraph _ _ _ _ _ _ _ _).1 entry with oldEntry | freshEntry
    · exact (mem_relationImage A B e y).1 (ZFSet.pair_mem_prod.1 (pushed.1 oldEntry)).1 |>.2
    · obtain ⟨_, _, _, n, hn, _, stamp⟩ := freshEntry
      obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
      exact (ZFSet.mem_irrefl t (before n t stamp)).elim

end PartitionPilot.Forcing

end OAI
