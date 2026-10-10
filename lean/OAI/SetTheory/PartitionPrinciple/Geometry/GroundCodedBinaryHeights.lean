import OAI.SetTheory.PartitionPrinciple.Definability.PrincipalTileRealization
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundIdealProjections
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundCompressionHeightSteps
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundRequestedCompressionTiles

namespace OAI

open scoped ZFSet


namespace PartitionPilot.Forcing
open SetFormula
universe u

structure StrictHeightGraphCode (L H rL rH h : ZFSet.{u}) : Prop where
  function : ZFSet.IsFunc L H h
  strict : ∀ x ∈ L, ∀ y ∈ L, x ≠ y → ZFSet.pair x y ∈ rL →
    ∀ a b, ZFSet.pair x a ∈ h → ZFSet.pair y b ∈ h → ZFSet.pair a b ∈ rH

theorem StrictLexHeightCode.strictHeightGraph {L C D r h rD : ZFSet.{u}}
    (code : StrictLexHeightCode L C D r h rD) :
    StrictHeightGraphCode L (ZFSet.prod C D) r (lexHeightOrder C D rD) h := by
  refine ⟨code.function, ?_⟩
  intro x hx y hy different lower a b first second
  obtain ⟨c, hc, q, hq, eq⟩ := ZFSet.mem_prod.1 (ZFSet.pair_mem_prod.1 (code.function.1 first)).2
  obtain ⟨d, hd, v, hv, eq'⟩ := ZFSet.mem_prod.1 (ZFSet.pair_mem_prod.1 (code.function.1 second)).2
  subst a
  subst b
  exact (pair_mem_lexHeightOrder _ _ _ _ _ _ _).2
    ⟨hc, hq, hd, hv, code.strict x hx y hy c q d v lower different first second⟩

namespace TransitiveGround

theorem exists_groundHeightInterpolation (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    {L H rL rH seed D rD c lo hi : ZFSet.{u}}
    (hL : L ∈ M.sets) (hH : H ∈ M.sets) (hrH : rH ∈ M.sets) (hSeed : seed ∈ M.sets)
    (hD : D ∈ M.sets) (hrD : rD ∈ M.sets) (hc : c ∈ M.sets)
    (seedCode : StrictHeightGraphCode L H rL rH seed)
    (linear : StrictLinearOrderCode H rH) (target : DenseOrderCode D rD)
    (injection : InjectionCode D ZFSet.omega c)
    (small : M.groundEmbeddable (relationImage L H seed) ZFSet.omega)
    (hlo : lo ∈ D) (hhi : hi ∈ D) (gap : ZFSet.pair lo hi ∈ rD) :
    ∃ height ∈ M.sets, StrictHeightGraphCode L D rL rD height ∧
      (∀ x z, ZFSet.pair x z ∈ height → ZFSet.pair lo z ∈ rD ∧ ZFSet.pair z hi ∈ rD) ∧
      relationImage L D height ∈ M.sets ∧
      M.groundEmbeddable (relationImage L D height) ZFSet.omega ∧
      ∀ x y a b q z, ZFSet.pair x a ∈ seed → ZFSet.pair y b ∈ seed →
        ZFSet.pair x q ∈ height → ZFSet.pair y z ∈ height →
          (a = b ↔ q = z) ∧ (ZFSet.pair a b ∈ rH ↔ ZFSet.pair q z ∈ rD) := by
  let R := relationImage L H seed
  have hR := M.relationImage_mem separation hL hH hSeed
  have hOrder : heightOrderRestriction R rH ∈ M.sets :=
    M.injection_restriction_mem separation hR hR hrH
  have rLinear : StrictLinearOrderCode R (heightOrderRestriction R rH) :=
    heightOrderRestriction_linear linear (fun _ h => ((mem_relationImage L H seed _).1 h).1)
  obtain ⟨e, he, embedding⟩ := M.exists_intervalEmbedding pairing unions powers separation collection infinite
    hR hD hOrder hrD hc rLinear target injection small hlo hhi gap
  let height := relationCompose L R D seed e
  have function := relationCompose_function_of_subset (function_on_relationImage seedCode.function)
    embedding.injection.function (fun _ h => h)
  have ground : height ∈ M.sets := M.relationCompose_mem pairing unions powers separation hL hR hD hSeed he
  have liftEntry {x a z : ZFSet.{u}} (source : ZFSet.pair x a ∈ seed)
      (entry : ZFSet.pair x z ∈ height) : ZFSet.pair a z ∈ e := by
    obtain ⟨_, _, a', _, other, image⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 entry
    obtain ⟨v, _, unique⟩ := seedCode.function.2 x (ZFSet.pair_mem_prod.1 (seedCode.function.1 source)).1
    have equal := (unique a source).trans (unique a' other).symm
    exact equal.symm ▸ image
  have exactOrder {x y a b q z : ZFSet.{u}}
      (first : ZFSet.pair x a ∈ seed) (second : ZFSet.pair y b ∈ seed)
      (left : ZFSet.pair x q ∈ height) (right : ZFSet.pair y z ∈ height) :
      (a = b ↔ q = z) ∧ (ZFSet.pair a b ∈ rH ↔ ZFSet.pair q z ∈ rD) := by
    have aq := liftEntry first left
    have bz := liftEntry second right
    have aR := (ZFSet.pair_mem_prod.1 (embedding.injection.function.1 aq)).1
    have bR := (ZFSet.pair_mem_prod.1 (embedding.injection.function.1 bz)).1
    refine ⟨?_, ?_⟩
    · constructor
      · intro equal
        subst b
        obtain ⟨v, _, unique⟩ := embedding.injection.function.2 a aR
        exact (unique q aq).trans (unique z bz).symm
      · intro equal
        subst z
        exact embedding.injection.injective a b q aq bz
    · have order := embedding.order a b q z aq bz
      rw [pair_mem_heightOrderRestriction] at order
      exact ⟨fun hab => order.1 ⟨hab, aR, bR⟩, fun hqz => (order.2 hqz).1⟩
  refine ⟨height, ground, ⟨function, ?_⟩, ?_, M.relationImage_mem separation hL hD ground, ?_, ?_⟩
  · intro x hx y hy different lower q z left right
    obtain ⟨a, ax, _⟩ := seedCode.function.2 x hx
    obtain ⟨b, byEntry, _⟩ := seedCode.function.2 y hy
    exact (exactOrder ax byEntry left right).2.1 (seedCode.strict x hx y hy different lower a b ax byEntry)
  · intro x z entry
    obtain ⟨_, _, a, _, _, az⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 entry
    exact embedding.inside a z az
  · exact M.groundEmbeddable_restrict separation (M.relationImage_mem separation hL hD ground)
      (M.omega_mem separation infinite) (fun _ h => (mem_relationImage _ _ _ _).1 h |>.1) ⟨c, hc, injection⟩
  · intro x y a b q z first second left right
    exact exactOrder first second left right

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open Compression.RecursiveMaps
universe u

noncomputable def lexProductOrder (C D rC rD : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ c ∈ C, ∃ q ∈ D, ∃ d ∈ C, ∃ v ∈ D,
    z = ZFSet.pair (ZFSet.pair c q) (ZFSet.pair d v) ∧
      (ZFSet.pair c d ∈ rC ∨ (c = d ∧ ZFSet.pair q v ∈ rD)))
    (ZFSet.prod (ZFSet.prod C D) (ZFSet.prod C D))

theorem mem_lexProductOrder (C D rC rD z : ZFSet.{u}) :
    z ∈ lexProductOrder C D rC rD ↔
      ∃ c ∈ C, ∃ q ∈ D, ∃ d ∈ C, ∃ v ∈ D,
        z = ZFSet.pair (ZFSet.pair c q) (ZFSet.pair d v) ∧
          (ZFSet.pair c d ∈ rC ∨ (c = d ∧ ZFSet.pair q v ∈ rD)) := by
  constructor
  · exact fun h => (ZFSet.mem_sep.1 h).2
  · rintro ⟨c, hc, q, hq, d, hd, v, hv, rfl, lower⟩
    exact ZFSet.mem_sep.2 ⟨ZFSet.pair_mem_prod.2
      ⟨ZFSet.pair_mem_prod.2 ⟨hc, hq⟩, ZFSet.pair_mem_prod.2 ⟨hd, hv⟩⟩,
      c, hc, q, hq, d, hd, v, hv, rfl, lower⟩

theorem pair_mem_lexProductOrder (C D rC rD c q d v : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair c q) (ZFSet.pair d v) ∈ lexProductOrder C D rC rD ↔
      c ∈ C ∧ q ∈ D ∧ d ∈ C ∧ v ∈ D ∧ (ZFSet.pair c d ∈ rC ∨ (c = d ∧ ZFSet.pair q v ∈ rD)) := by
  rw [mem_lexProductOrder]
  constructor
  · rintro ⟨c', hc, q', hq, d', hd, v', hv, equal, lower⟩
    obtain ⟨left, right⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 left
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 right
    exact ⟨hc, hq, hd, hv, lower⟩
  · rintro ⟨hc, hq, hd, hv, lower⟩
    exact ⟨c, hc, q, hq, d, hd, v, hv, rfl, lower⟩

theorem lexProductOrder_code {C D rC rD : ZFSet.{u}}
    (columns : StrictLinearOrderCode C rC) (target : StrictLinearOrderCode D rD) :
    StrictLinearOrderCode (ZFSet.prod C D) (lexProductOrder C D rC rD) := by
  refine ⟨fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_, ?_, ?_⟩
  · intro x hx hxx
    obtain ⟨c, _, q, hq, rfl⟩ := ZFSet.mem_prod.1 hx
    rcases ((pair_mem_lexProductOrder C D rC rD c q c q).1 hxx).2.2.2.2 with less | same
    · exact columns.irrefl c (ZFSet.pair_mem_prod.1 (columns.shape less)).1 less
    · exact target.irrefl q hq same.2
  · intro x y z hxy hyz
    have xy := ZFSet.pair_mem_prod.1 (ZFSet.mem_sep.1 hxy).1
    have yz := ZFSet.pair_mem_prod.1 (ZFSet.mem_sep.1 hyz).1
    obtain ⟨c, hc, q, hq, rfl⟩ := ZFSet.mem_prod.1 xy.1
    obtain ⟨d, _, v, _, rfl⟩ := ZFSet.mem_prod.1 xy.2
    obtain ⟨b, hb, w, hw, rfl⟩ := ZFSet.mem_prod.1 yz.2
    have left := ((pair_mem_lexProductOrder C D rC rD c q d v).1 hxy).2.2.2.2
    have right := ((pair_mem_lexProductOrder C D rC rD d v b w).1 hyz).2.2.2.2
    apply (pair_mem_lexProductOrder C D rC rD c q b w).2
    refine ⟨hc, hq, hb, hw, ?_⟩
    rcases left with lower | ⟨same, inside⟩
    · rcases right with lower' | ⟨same', _⟩
      · exact Or.inl (columns.trans c d b lower lower')
      · exact Or.inl (same' ▸ lower)
    · rcases right with lower' | ⟨same', inside'⟩
      · exact Or.inl (same.symm ▸ lower')
      · exact Or.inr ⟨same.trans same', target.trans q v w inside inside'⟩
  · intro x hx y hy
    obtain ⟨c, hc, q, hq, rfl⟩ := ZFSet.mem_prod.1 hx
    obtain ⟨d, hd, v, hv, rfl⟩ := ZFSet.mem_prod.1 hy
    rcases columns.compare c hc d hd with lower | same | greater
    · exact Or.inl ((pair_mem_lexProductOrder C D rC rD c q d v).2 ⟨hc, hq, hd, hv, Or.inl lower⟩)
    · subst d
      rcases target.compare q hq v hv with lower | same | greater
      · exact Or.inl ((pair_mem_lexProductOrder C D rC rD c q c v).2
          ⟨hc, hq, hc, hv, Or.inr ⟨rfl, lower⟩⟩)
      · exact Or.inr (Or.inl (congrArg (ZFSet.pair c) same))
      · exact Or.inr (Or.inr ((pair_mem_lexProductOrder C D rC rD c v c q).2
          ⟨hc, hv, hc, hq, Or.inr ⟨rfl, greater⟩⟩))
    · exact Or.inr (Or.inr ((pair_mem_lexProductOrder C D rC rD d v c q).2
        ⟨hd, hv, hc, hq, Or.inl greater⟩))

namespace BoundedFormula

def lexProductEntryFormula {n} (z C D rC rD : Fin n) : BoundedFormula n :=
  let lift (i : Fin n) := i.succ.succ.succ.succ
  exMem C (exMem D.succ (exMem C.succ.succ (exMem D.succ.succ.succ
    (.conj (pairOfPairsFormula (lift z) 3 2 1 0)
      (disj (pairMembershipFormula 3 1 (lift rC)) (.conj (.equal 3 1) (pairMembershipFormula 2 0 (lift rD))))))))

theorem truth_lexProductEntryFormula {n} (z C D rC rD : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (lexProductEntryFormula z C D rC rD) env ↔
      ∃ c ∈ env C, ∃ q ∈ env D, ∃ d ∈ env C, ∃ v ∈ env D,
        env z = ZFSet.pair (ZFSet.pair c q) (ZFSet.pair d v) ∧
          (ZFSet.pair c d ∈ env rC ∨ (c = d ∧ ZFSet.pair q v ∈ env rD)) := by
  simp only [lexProductEntryFormula, truth_exMem, Truth, truth_disj,
    truth_pairOfPairsFormula, truth_pairMembershipFormula]
  rfl

end BoundedFormula

namespace TransitiveGround

open SetFormula

theorem lexProductOrder_mem (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {C D rC rD : ZFSet.{u}} (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrC : rC ∈ M.sets) (hrD : rD ∈ M.sets) :
    lexProductOrder C D rC rD ∈ M.sets := by
  have carrier := M.prod_mem pairing unions powers separation hC hD
  let params := extend C (extend D (extend rC (extend rD Fin.elim0)))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.lexProductEntryFormula 0 1 2 3 4) params
    (Fin.cases hC (Fin.cases hD (Fin.cases hrC (Fin.cases hrD (fun i => Fin.elim0 i)))))
    (M.prod_mem pairing unions powers separation carrier carrier)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.lexProductEntryFormula 0 1 2 3 4) (extend z params))
      (ZFSet.prod (ZFSet.prod C D) (ZFSet.prod C D)) = lexProductOrder C D rC rD := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, lexProductOrder, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_lexProductEntryFormula 0 1 2 3 4 _)
  exact equal ▸ selected

end TransitiveGround

end PartitionPilot.Forcing


section

namespace PartitionPilot.Forcing
open SetRealization Compression.RecursiveMaps SetFormula
universe u

noncomputable def StrictLinearOrderCode.smallOrder {H rH : ZFSet.{u}}
    (code : StrictLinearOrderCode H rH) : LinearHeightOrder (SetMembers H) where
  lt x y := ZFSet.pair (SetMembers.raw x) (SetMembers.raw y) ∈ rH
  irrefl x := code.irrefl _ (SetMembers.raw_mem x)
  trans {x y z} := code.trans (SetMembers.raw x) (SetMembers.raw y) (SetMembers.raw z)
  compare x y := (code.compare _ (SetMembers.raw_mem x) _ (SetMembers.raw_mem y)).imp id
    (fun h => h.imp (fun eq => SetMembers.raw_injective H eq) id)

noncomputable def StrictHeightGraphCode.smallHeight {L H rL rH h μ : ZFSet.{u}}
    (code : StrictHeightGraphCode L H rL rH h) (meet : MeetOrderCode L rL μ)
    (linear : StrictLinearOrderCode H rH) :
    StrictHeight meet.toSmallMeetOrder linear.smallOrder.toHeightOrder where
  value := (SetMembers.presentation L).decodeFunction (SetMembers.presentation H) h code.function
  strict x y lower different := code.strict _ (SetMembers.raw_mem x) _ (SetMembers.raw_mem y)
    (fun eq => different (SetMembers.raw_injective L eq)) lower _ _
    ((SetMembers.presentation L).decodeFunction_mem (SetMembers.presentation H) h code.function x)
    ((SetMembers.presentation L).decodeFunction_mem (SetMembers.presentation H) h code.function y)

theorem StrictHeightGraphCode.smallHeight_graph {L H rL rH h μ : ZFSet.{u}}
    (code : StrictHeightGraphCode L H rL rH h) (meet : MeetOrderCode L rL μ)
    (linear : StrictLinearOrderCode H rH) :
    (SetMembers.presentation L).graph (SetMembers.presentation H) (code.smallHeight meet linear).value = h :=
  (SetMembers.presentation L).graph_decodeFunction (SetMembers.presentation H) h code.function

end PartitionPilot.Forcing

namespace PartitionPilot.SetRealization.Presentation
open Forcing Compression.RecursiveMaps
universe u
variable {A B C : Type u}

theorem strictHeightGraphCode (s : Presentation A) (t : Presentation B)
    {P : MeetOrder A} {R : HeightOrder B} (height : StrictHeight P R)
    {r rH : ZFSet.{u}}
    (order : ∀ x y, ZFSet.pair (s.encode x) (s.encode y) ∈ r ↔ P.le x y)
    (target : ∀ a b, ZFSet.pair (t.encode a) (t.encode b) ∈ rH ↔ R.lt a b) :
    StrictHeightGraphCode s.carrier t.carrier r rH (s.graph t height.value) := by
  refine ⟨s.graph_isFunc t height.value, ?_⟩
  intro x hx y hy different lower a b first second
  obtain ⟨x, rfl⟩ := (s.mem_carrier x).1 hx
  obtain ⟨y, rfl⟩ := (s.mem_carrier y).1 hy
  obtain ⟨a, rfl⟩ := (t.mem_carrier a).1 (ZFSet.pair_mem_prod.1 ((s.graph_isFunc t height.value).1 first)).2
  obtain ⟨b, rfl⟩ := (t.mem_carrier b).1 (ZFSet.pair_mem_prod.1 ((s.graph_isFunc t height.value).1 second)).2
  have firstEq := (s.pair_mem_graph t height.value x a).1 first
  have secondEq := (s.pair_mem_graph t height.value y b).1 second
  rw [← firstEq, ← secondEq]
  exact (target _ _).2 (height.strict x y ((order x y).1 lower) (fun eq => different (congrArg s.encode eq)))

theorem lexProductOrder_iff (s : Presentation A) (t : Presentation B)
    (R : LinearHeightOrder A) (S : LinearHeightOrder B) {rR rS : ZFSet.{u}}
    (first : ∀ a b, ZFSet.pair (s.encode a) (s.encode b) ∈ rR ↔ R.lt a b)
    (second : ∀ a b, ZFSet.pair (t.encode a) (t.encode b) ∈ rS ↔ S.lt a b) (x y : A × B) :
    ZFSet.pair ((s.product t).encode x) ((s.product t).encode y) ∈
      lexProductOrder s.carrier t.carrier rR rS ↔ (R.lex S).lt x y := by
  change ZFSet.pair (ZFSet.pair (s.encode x.1) (t.encode x.2))
    (ZFSet.pair (s.encode y.1) (t.encode y.2)) ∈ _ ↔ _
  rw [pair_mem_lexProductOrder]
  simp only [s.encode_mem, t.encode_mem, true_and, first, second, s.injective.eq_iff]
  rfl

theorem compose_graphs (s : Presentation A) (t : Presentation B) (v : Presentation C)
    (f : A → B) (g : B → C) :
    relationCompose s.carrier t.carrier v.carrier (s.graph t f) (t.graph v g) =
      s.graph v (fun x => g (f x)) := by
  apply ZFSet.ext
  intro z
  rw [mem_relationCompose, Presentation.mem_graph]
  constructor
  · rintro ⟨x, hx, y, hy, w, hw, rfl, first, second⟩
    obtain ⟨a, rfl⟩ := (s.mem_carrier x).1 hx
    obtain ⟨b, rfl⟩ := (t.mem_carrier y).1 hy
    obtain ⟨c, rfl⟩ := (v.mem_carrier w).1 hw
    have ab := (s.pair_mem_graph t f a b).1 first
    have bc := (t.pair_mem_graph v g b c).1 second
    subst b
    subst c
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨s.encode a, s.encode_mem a, t.encode (f a), t.encode_mem _,
      v.encode (g (f a)), v.encode_mem _, rfl,
      (s.pair_mem_graph t f _ _).2 rfl, (t.pair_mem_graph v g _ _).2 rfl⟩

end PartitionPilot.SetRealization.Presentation

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable {A B C : Type u} (s : Presentation A) (t : Presentation B) (v : Presentation C)

include pairing unions powers separation

theorem composed_graph_mem (f : A → B) (g : B → C)
    (hs : s.carrier ∈ M.sets) (ht : t.carrier ∈ M.sets) (hv : v.carrier ∈ M.sets)
    (hf : s.graph t f ∈ M.sets) (hg : t.graph v g ∈ M.sets) :
    s.graph v (fun x => g (f x)) ∈ M.sets := by
  rw [← s.compose_graphs t v f g]
  exact M.relationCompose_mem pairing unions powers separation hs ht hv hf hg

theorem paired_graph_mem (f : A → B) (g : A → C)
    (hs : s.carrier ∈ M.sets) (ht : t.carrier ∈ M.sets) (hv : v.carrier ∈ M.sets)
    (hf : s.graph t f ∈ M.sets) (hg : s.graph v g ∈ M.sets) :
    s.graph (t.product v) (fun x => (f x, g x)) ∈ M.sets := by
  rw [← pairedGraph_eq s t v f g]
  exact M.pairedGraph_mem pairing unions powers separation hs ht hv hf hg

end PartitionPilot.Forcing.TransitiveGround

end


namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization Compression.RecursiveMaps SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
variable {A H : Type u} (s : Presentation A) (t : Presentation H)
variable {P : MeetOrder A} (top : A) (greatest : ∀ a, P.le a top)
variable (R : LinearHeightOrder H) (seed : StrictHeight P R.toHeightOrder)
variable (hP : s.carrier ∈ M.sets) (hH : t.carrier ∈ M.sets)
variable (hSeed : s.graph t seed.value ∈ M.sets)
variable (small : M.groundEmbeddable (relationImage s.carrier t.carrier (s.graph t seed.value)) ZFSet.omega)

include pairing unions powers separation infinite hP hH hSeed small

theorem binaryTuple_ground (tile : TileRequests.Tile P (ULift.{u} Unit))
    (q : Presentation tile.Space) {ν : ZFSet.{u}}
    (hL : q.carrier ∈ M.sets) (hν : ν ∈ M.sets)
    (meetFunction : ZFSet.IsFunc (ZFSet.prod q.carrier q.carrier) q.carrier ν)
    (meetEntries : ∀ x y, ZFSet.pair (ZFSet.pair (q.encode x) (q.encode y))
      (q.encode (tile.order.meet x y)) ∈ ν)
    (root : s.graph q tile.root.toFun ∈ M.sets)
    (child : s.graph q (tile.child ⟨()⟩).toFun ∈ M.sets) :
    let graph := q.graph (t.product t) (tile.binaryTuple top greatest R seed).value
    graph ∈ M.sets ∧ M.groundEmbeddable
      (relationImage q.carrier (t.product t).carrier graph) ZFSet.omega := by
  dsimp only
  have first := M.idealProjection_mem s q tile.root top meetFunction meetEntries
    pairing unions powers separation hP hL hν root
  have second := M.idealProjection_mem s q (tile.child ⟨()⟩) top meetFunction meetEntries
    pairing unions powers separation hP hL hν child
  have firstHeight := M.composed_graph_mem pairing unions powers separation q s t
    (tile.root.projection top) seed.value hL hP hH first hSeed
  have secondHeight := M.composed_graph_mem pairing unions powers separation q s t
    ((tile.child ⟨()⟩).projection top) seed.value hL hP hH second hSeed
  have graphGround : q.graph (t.product t) (tile.binaryTuple top greatest R seed).value ∈ M.sets :=
    M.paired_graph_mem pairing unions powers separation q t t _ _ hL hH hH firstHeight secondHeight
  refine ⟨graphGround, ?_⟩
  let E := relationImage s.carrier t.carrier (s.graph t seed.value)
  have hE : E ∈ M.sets := M.relationImage_mem separation hP hH hSeed
  have each (a : A) : t.encode (seed.value a) ∈ E :=
    (mem_relationImage _ _ _ _).2 ⟨t.encode_mem _, s.encode a, s.encode_mem a,
      (s.pair_mem_graph t seed.value _ _).2 rfl⟩
  apply M.groundEmbeddable_restrict separation
    (M.relationImage_mem separation hL (M.prod_mem pairing unions powers separation hH hH) graphGround)
    (M.omega_mem separation infinite) ?_
    (M.groundEmbeddable_product pairing unions powers separation infinite hE hE small small)
  intro z hz
  obtain ⟨_, x, hx, entry⟩ := (mem_relationImage _ _ _ _).1 hz
  obtain ⟨x, rfl⟩ := (q.mem_carrier x).1 hx
  obtain ⟨y, eq⟩ := (q.mem_graph (t.product t) (tile.binaryTuple top greatest R seed).value _).1 entry
  have parts := ZFSet.pair_inj.1 eq
  have xy := q.injective parts.1
  subst y
  rw [← parts.2]
  exact ZFSet.pair_mem_prod.2 ⟨each _, each _⟩

theorem rectangleTuple_ground (tile : TileRequests.Tile P (ULift.{u} Bool))
    (q : Presentation tile.Space) {ν : ZFSet.{u}}
    (hL : q.carrier ∈ M.sets) (hν : ν ∈ M.sets)
    (meetFunction : ZFSet.IsFunc (ZFSet.prod q.carrier q.carrier) q.carrier ν)
    (meetEntries : ∀ x y, ZFSet.pair (ZFSet.pair (q.encode x) (q.encode y))
      (q.encode (tile.order.meet x y)) ∈ ν)
    (root : s.graph q tile.root.toFun ∈ M.sets)
    (first : s.graph q (tile.child ⟨false⟩).toFun ∈ M.sets)
    (second : s.graph q (tile.child ⟨true⟩).toFun ∈ M.sets) :
    let graph := q.graph (t.product (t.product t)) (tile.rectangleTuple top greatest R seed).value
    graph ∈ M.sets ∧ M.groundEmbeddable
      (relationImage q.carrier (t.product (t.product t)).carrier graph) ZFSet.omega := by
  dsimp only
  have project (e : IdealEmbedding P tile.order) (he : s.graph q e.toFun ∈ M.sets) :=
    M.composed_graph_mem pairing unions powers separation q s t (e.projection top) seed.value
      hL hP hH (M.idealProjection_mem s q e top meetFunction meetEntries
        pairing unions powers separation hP hL hν he) hSeed
  have pairGround := M.paired_graph_mem pairing unions powers separation q t t _ _ hL hH hH
    (project (tile.child ⟨false⟩) first) (project (tile.child ⟨true⟩) second)
  have hHH := M.prod_mem pairing unions powers separation hH hH
  have graphGround : q.graph (t.product (t.product t)) (tile.rectangleTuple top greatest R seed).value ∈ M.sets :=
    M.paired_graph_mem pairing unions powers separation q t (t.product t) _ _ hL hH hHH
      (project tile.root root) pairGround
  refine ⟨graphGround, ?_⟩
  let E := relationImage s.carrier t.carrier (s.graph t seed.value)
  have hE : E ∈ M.sets := M.relationImage_mem separation hP hH hSeed
  have each (a : A) : t.encode (seed.value a) ∈ E :=
    (mem_relationImage _ _ _ _).2 ⟨t.encode_mem _, s.encode a, s.encode_mem a,
      (s.pair_mem_graph t seed.value _ _).2 rfl⟩
  have smallEE := M.groundEmbeddable_product pairing unions powers separation infinite hE hE small small
  have smallEEE := M.groundEmbeddable_product pairing unions powers separation infinite hE
    (M.prod_mem pairing unions powers separation hE hE) small smallEE
  apply M.groundEmbeddable_restrict separation
    (M.relationImage_mem separation hL (M.prod_mem pairing unions powers separation hH hHH) graphGround)
    (M.omega_mem separation infinite) ?_ smallEEE
  intro z hz
  obtain ⟨_, x, hx, entry⟩ := (mem_relationImage _ _ _ _).1 hz
  obtain ⟨x, rfl⟩ := (q.mem_carrier x).1 hx
  obtain ⟨y, eq⟩ := (q.mem_graph (t.product (t.product t)) (tile.rectangleTuple top greatest R seed).value _).1 entry
  have parts := ZFSet.pair_inj.1 eq
  have xy := q.injective parts.1
  subst y
  rw [← parts.2]
  exact ZFSet.pair_mem_prod.2 ⟨each _, ZFSet.pair_mem_prod.2 ⟨each _, each _⟩⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing
open SetRealization Compression.RecursiveMaps SetFormula
universe u

structure IntervalHeightCode (L r D rD lo hi height : ZFSet.{u}) : Prop
    extends StrictHeightGraphCode L D r rD height where
  inside : ∀ x z, ZFSet.pair x z ∈ height → ZFSet.pair lo z ∈ rD ∧ ZFSet.pair z hi ∈ rD

theorem StrictHeightGraphCode.weak {L H r rH h : ZFSet.{u}}
    (code : StrictHeightGraphCode L H r rH h) {x y a b : ZFSet.{u}}
    (lower : ZFSet.pair x y ∈ r) (first : ZFSet.pair x a ∈ h) (second : ZFSet.pair y b ∈ h) :
    a = b ∨ ZFSet.pair a b ∈ rH := by
  have hx := (ZFSet.pair_mem_prod.1 (code.function.1 first)).1
  have hy := (ZFSet.pair_mem_prod.1 (code.function.1 second)).1
  by_cases equal : x = y
  · subst y
    obtain ⟨v, _, unique⟩ := code.function.2 x hx
    exact Or.inl ((unique a first).trans (unique b second).symm)
  · exact Or.inr (code.strict x hx y hy equal lower a b first second)

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets) (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
variable {A H : Type u} (s : Presentation A) (t : Presentation H)
variable {P : MeetOrder A} (top : A) (greatest : ∀ a, P.le a top)
variable (R : LinearHeightOrder H) (seed : StrictHeight P R.toHeightOrder)
variable {rH D rD c lo hi : ZFSet.{u}}
variable (heightOrder : ∀ a b, ZFSet.pair (t.encode a) (t.encode b) ∈ rH ↔ R.lt a b)
variable (linear : StrictLinearOrderCode t.carrier rH)
variable (target : DenseOrderCode D rD) (injection : InjectionCode D ZFSet.omega c)
variable (hP : s.carrier ∈ M.sets) (hH : t.carrier ∈ M.sets)
variable (hSeed : s.graph t seed.value ∈ M.sets) (hrH : rH ∈ M.sets)
variable (hD : D ∈ M.sets) (hrD : rD ∈ M.sets) (hc : c ∈ M.sets)
variable (small : M.groundEmbeddable (relationImage s.carrier t.carrier (s.graph t seed.value)) ZFSet.omega)
variable (hlo : lo ∈ D) (hhi : hi ∈ D) (gap : ZFSet.pair lo hi ∈ rD)
include top greatest pairing unions powers separation collection infinite heightOrder linear target injection
  hP hH hSeed hrH hD hrD hc small hlo hhi gap

theorem exists_binaryTileIntervalHeight (tile : TileRequests.Tile P (ULift.{u} Unit))
    (q : Presentation tile.Space) {r ν : ZFSet.{u}}
    (hL : q.carrier ∈ M.sets) (hν : ν ∈ M.sets)
    (related : ∀ x y, ZFSet.pair (q.encode x) (q.encode y) ∈ r ↔ tile.order.le x y)
    (meetFunction : ZFSet.IsFunc (ZFSet.prod q.carrier q.carrier) q.carrier ν)
    (meetEntries : ∀ x y, ZFSet.pair (ZFSet.pair (q.encode x) (q.encode y))
      (q.encode (tile.order.meet x y)) ∈ ν)
    (root : s.graph q tile.root.toFun ∈ M.sets)
    (child : s.graph q (tile.child ⟨()⟩).toFun ∈ M.sets) :
    ∃ height ∈ M.sets, IntervalHeightCode q.carrier r D rD lo hi height ∧
      relationImage q.carrier D height ∈ M.sets ∧
      M.groundEmbeddable (relationImage q.carrier D height) ZFSet.omega := by
  have tuple := M.binaryTuple_ground pairing unions powers separation infinite s t top greatest R seed
    hP hH hSeed small tile q hL hν meetFunction meetEntries root child
  have strict := q.strictHeightGraphCode (t.product t) (tile.binaryTuple top greatest R seed) related
    (t.lexProductOrder_iff t R R heightOrder heightOrder)
  obtain ⟨height, ground, code, inside, rangeGround, rangeSmall, _⟩ :=
    M.exists_groundHeightInterpolation pairing unions powers separation collection infinite hL
      (M.prod_mem pairing unions powers separation hH hH)
      (M.lexProductOrder_mem pairing unions powers separation hH hH hrH hrH) tuple.1
      hD hrD hc strict (lexProductOrder_code linear linear) target injection tuple.2 hlo hhi gap
  exact ⟨height, ground, ⟨code, inside⟩, rangeGround, rangeSmall⟩

theorem exists_rectangleTileIntervalHeight (tile : TileRequests.Tile P (ULift.{u} Bool))
    (q : Presentation tile.Space) {r ν : ZFSet.{u}}
    (hL : q.carrier ∈ M.sets) (hν : ν ∈ M.sets)
    (related : ∀ x y, ZFSet.pair (q.encode x) (q.encode y) ∈ r ↔ tile.order.le x y)
    (meetFunction : ZFSet.IsFunc (ZFSet.prod q.carrier q.carrier) q.carrier ν)
    (meetEntries : ∀ x y, ZFSet.pair (ZFSet.pair (q.encode x) (q.encode y))
      (q.encode (tile.order.meet x y)) ∈ ν)
    (root : s.graph q tile.root.toFun ∈ M.sets)
    (first : s.graph q (tile.child ⟨false⟩).toFun ∈ M.sets)
    (second : s.graph q (tile.child ⟨true⟩).toFun ∈ M.sets) :
    ∃ height ∈ M.sets, IntervalHeightCode q.carrier r D rD lo hi height ∧
      relationImage q.carrier D height ∈ M.sets ∧
      M.groundEmbeddable (relationImage q.carrier D height) ZFSet.omega := by
  have tuple := M.rectangleTuple_ground pairing unions powers separation infinite s t top greatest R seed
    hP hH hSeed small tile q hL hν meetFunction meetEntries root first second
  have inner := t.lexProductOrder_iff t R R heightOrder heightOrder
  have strict := q.strictHeightGraphCode (t.product (t.product t)) (tile.rectangleTuple top greatest R seed) related
    (t.lexProductOrder_iff (t.product t) R (R.lex R) heightOrder inner)
  have hHH := M.prod_mem pairing unions powers separation hH hH
  have hrHH := M.lexProductOrder_mem pairing unions powers separation hH hH hrH hrH
  obtain ⟨height, ground, code, inside, rangeGround, rangeSmall, _⟩ :=
    M.exists_groundHeightInterpolation pairing unions powers separation collection infinite hL
      (M.prod_mem pairing unions powers separation hH hHH)
      (M.lexProductOrder_mem pairing unions powers separation hH hHH hrH hrHH) tuple.1
      hD hrD hc strict (lexProductOrder_code linear (lexProductOrder_code linear linear))
      target injection tuple.2 hlo hhi gap
  exact ⟨height, ground, ⟨code, inside⟩, rangeGround, rangeSmall⟩

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization Compression.RecursiveMaps SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets) (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
variable {A H : Type u} (s : Presentation A) (t : Presentation H)
variable {P : MeetOrder A} (top : A) (greatest : ∀ a, P.le a top)
variable (R : LinearHeightOrder H) (seed : StrictHeight P R.toHeightOrder)
variable {rH D rD c lo hi : ZFSet.{u}}
variable (heightOrder : ∀ a b, ZFSet.pair (t.encode a) (t.encode b) ∈ rH ↔ R.lt a b)
variable (linear : StrictLinearOrderCode t.carrier rH)
variable (target : DenseOrderCode D rD) (injection : InjectionCode D ZFSet.omega c)
variable (hP : s.carrier ∈ M.sets) (hH : t.carrier ∈ M.sets)
variable (hSeed : s.graph t seed.value ∈ M.sets) (hrH : rH ∈ M.sets)
variable (hD : D ∈ M.sets) (hrD : rD ∈ M.sets) (hc : c ∈ M.sets)
variable (small : M.groundEmbeddable (relationImage s.carrier t.carrier (s.graph t seed.value)) ZFSet.omega)
variable (hlo : lo ∈ D) (hhi : hi ∈ D) (gap : ZFSet.pair lo hi ∈ rD)
include top greatest pairing unions powers separation collection infinite heightOrder linear target injection
  hP hH hSeed hrH hD hrD hc small hlo hhi gap

theorem exists_requestTileIntervalHeight (request : TileRequests.Request P)
    (q : Presentation (request.tile top greatest).Space) {r ν : ZFSet.{u}}
    (hL : q.carrier ∈ M.sets) (hν : ν ∈ M.sets)
    (related : ∀ x y, ZFSet.pair (q.encode x) (q.encode y) ∈ r ↔ (request.tile top greatest).order.le x y)
    (meetFunction : ZFSet.IsFunc (ZFSet.prod q.carrier q.carrier) q.carrier ν)
    (meetEntries : ∀ x y, ZFSet.pair (ZFSet.pair (q.encode x) (q.encode y))
      (q.encode ((request.tile top greatest).order.meet x y)) ∈ ν)
    (root : s.graph q (request.tile top greatest).root.toFun ∈ M.sets)
    (children : ∀ j, s.graph q ((request.tile top greatest).child j).toFun ∈ M.sets) :
    ∃ height ∈ M.sets, IntervalHeightCode q.carrier r D rD lo hi height ∧
      relationImage q.carrier D height ∈ M.sets ∧
      M.groundEmbeddable (relationImage q.carrier D height) ZFSet.omega := by
  cases request with
  | separation W =>
    exact M.exists_binaryTileIntervalHeight pairing unions powers separation collection infinite s t top greatest R seed
      heightOrder linear target injection hP hH hSeed hrH hD hrD hc small hlo hhi gap
      _ q hL hν related meetFunction meetEntries root (children ⟨()⟩)
  | compression K copy =>
    exact M.exists_binaryTileIntervalHeight pairing unions powers separation collection infinite s t top greatest R seed
      heightOrder linear target injection hP hH hSeed hrH hD hrD hc small hlo hhi gap
      _ q hL hν related meetFunction meetEntries root (children ⟨()⟩)
  | rectangle data =>
    exact M.exists_rectangleTileIntervalHeight pairing unions powers separation collection infinite s t top greatest R seed
      heightOrder linear target injection hP hH hSeed hrH hD hrD hc small hlo hhi gap
      _ q hL hν related meetFunction meetEntries root (children ⟨false⟩) (children ⟨true⟩)

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing
universe u

def intervalHeightCandidate (Ps rs D rD lo hi i f : ZFSet.{u}) : Prop :=
  ∃ P ∈ ⋃₀ ⋃₀ Ps, ∃ r ∈ ⋃₀ ⋃₀ rs,
    ZFSet.pair i P ∈ Ps ∧ ZFSet.pair i r ∈ rs ∧ IntervalHeightCode P r D rD lo hi f

noncomputable def intervalHeightRelation (I W Ps rs D rD lo hi : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ i ∈ I, ∃ f ∈ W, z = ZFSet.pair i f ∧
    intervalHeightCandidate Ps rs D rD lo hi i f) (ZFSet.prod I W)

theorem pair_mem_intervalHeightRelation (I W Ps rs D rD lo hi i f : ZFSet.{u}) :
    ZFSet.pair i f ∈ intervalHeightRelation I W Ps rs D rD lo hi ↔
      i ∈ I ∧ f ∈ W ∧ intervalHeightCandidate Ps rs D rD lo hi i f := by
  rw [intervalHeightRelation, ZFSet.mem_sep, ZFSet.pair_mem_prod]
  constructor
  · rintro ⟨⟨hi, hf⟩, j, _, g, _, equal, valid⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hi, hf, valid⟩
  · rintro ⟨hi, hf, valid⟩
    exact ⟨⟨hi, hf⟩, i, hi, f, hf, rfl, valid⟩

theorem intervalHeightCandidate_iff {I Ps rs D rD lo hi : ZFSet.{u}}
    (sources : FunctionGraphOn I Ps) (orders : FunctionGraphOn I rs)
    (i : {i : ZFSet.{u} // i ∈ I}) (f : ZFSet.{u}) :
    intervalHeightCandidate Ps rs D rD lo hi i.val f ↔
      IntervalHeightCode (sources.value i) (orders.value i) D rD lo hi f := by
  constructor
  · rintro ⟨P, _, r, _, pEntry, rEntry, code⟩
    rw [sources.value_eq_of_entry i pEntry, orders.value_eq_of_entry i rEntry]
    exact code
  · intro code
    exact ⟨sources.value i, sources.value_mem_doubleUnion i,
      orders.value i, orders.value_mem_doubleUnion i,
      sources.value_entry i, orders.value_entry i, code⟩

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization Compression.RecursiveMaps SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets) (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
variable {P r μ H rH old D rD c lo hi : ZFSet.{u}}
variable (source : MeetOrderCode P r μ) (top : SetMembers P)
variable (greatest : ∀ x, source.toSmallMeetOrder.le x top)
variable (height : StrictHeightGraphCode P H r rH old) (linear : StrictLinearOrderCode H rH)
variable (target : DenseOrderCode D rD) (injection : InjectionCode D ZFSet.omega c)
variable (hP : P ∈ M.sets) (hH : H ∈ M.sets) (hOld : old ∈ M.sets) (hrH : rH ∈ M.sets)
variable (hD : D ∈ M.sets) (hrD : rD ∈ M.sets) (hc : c ∈ M.sets)
variable (small : M.groundEmbeddable (relationImage P H old) ZFSet.omega)
variable (hlo : lo ∈ D) (hhi : hi ∈ D) (gap : ZFSet.pair lo hi ∈ rD)
include pairing unions powers separation collection infinite top greatest
  height linear target injection hP hH hOld hrH hD hrD hc small hlo hhi gap

theorem exists_codedBinaryTileHeight {L v ν first second : ZFSet.{u}}
    (tileMeet : MeetOrderCode L v ν) (hL : L ∈ M.sets) (hν : ν ∈ M.sets)
    (left : MeetEmbeddingCode P L r v μ ν first) (right : MeetEmbeddingCode P L r v μ ν second)
    (hFirst : first ∈ M.sets) (hSecond : second ∈ M.sets)
    (leftIdeal : ∀ x y z, ZFSet.pair x y ∈ first → z ∈ L → ZFSet.pair z y ∈ v →
      ∃ a ∈ P, ZFSet.pair a z ∈ first)
    (rightIdeal : ∀ x y z, ZFSet.pair x y ∈ second → z ∈ L → ZFSet.pair z y ∈ v →
      ∃ a ∈ P, ZFSet.pair a z ∈ second)
    (cover : ∀ z ∈ L, (∃ x ∈ P, ZFSet.pair x z ∈ first) ∨ ∃ x ∈ P, ZFSet.pair x z ∈ second) :
    ∃ h ∈ M.sets, IntervalHeightCode L v D rD lo hi h ∧ relationImage L D h ∈ M.sets ∧
      M.groundEmbeddable (relationImage L D h) ZFSet.omega := by
  let tile := binaryTileOfCodes source tileMeet left right leftIdeal rightIdeal cover
  have seedGround : (SetMembers.presentation P).graph (SetMembers.presentation H)
      (height.smallHeight source linear).value ∈ M.sets := by
    rw [height.smallHeight_graph]
    exact hOld
  have seedSmall : M.groundEmbeddable (relationImage P H
      ((SetMembers.presentation P).graph (SetMembers.presentation H) (height.smallHeight source linear).value)) ZFSet.omega := by
    rw [height.smallHeight_graph]
    exact small
  have leftGround : (SetMembers.presentation P).graph (SetMembers.presentation L) tile.root.toFun ∈ M.sets := by
    change (SetMembers.presentation P).graph (SetMembers.presentation L) left.smallValue ∈ M.sets
    rw [left.smallValue_graph]
    exact hFirst
  have rightGround : (SetMembers.presentation P).graph (SetMembers.presentation L) (tile.child ⟨()⟩).toFun ∈ M.sets := by
    change (SetMembers.presentation P).graph (SetMembers.presentation L) right.smallValue ∈ M.sets
    rw [right.smallValue_graph]
    exact hSecond
  exact M.exists_binaryTileIntervalHeight pairing unions powers separation collection infinite
    (SetMembers.presentation P) (SetMembers.presentation H) top greatest linear.smallOrder
    (height.smallHeight source linear) (fun _ _ => Iff.rfl) linear target injection
    hP hH seedGround hrH hD hrD hc seedSmall hlo hhi gap tile (SetMembers.presentation L)
    hL hν (fun _ _ => Iff.rfl) tileMeet.operation tileMeet.smallMeet_entry leftGround rightGround

theorem exists_separationTileHeight {W : ZFSet.{u}}
    (hr : r ∈ M.sets) (hμ : μ ∈ M.sets) (hW : W ∈ P) :
    ∃ h ∈ M.sets, IntervalHeightCode (separationTileCarrier P r W) (separationTileOrder P r μ W)
      D rD lo hi h ∧ relationImage (separationTileCarrier P r W) D h ∈ M.sets ∧
      M.groundEmbeddable (relationImage (separationTileCarrier P r W) D h) ZFSet.omega := by
  let tile := separationTileCoding source ⟨W, hW⟩
  have ground := M.separationTile_ground pairing unions powers separation source hP hr hμ hW
  have embeddings := separationTile_embeddings source hW
  apply M.exists_codedBinaryTileHeight pairing unions powers separation collection infinite
    source top greatest height linear target injection hP hH hOld hrH hD hrD hc small hlo hhi gap
    tile.meetOrder ground.1 ground.2.2.1 embeddings.1 embeddings.2 ground.2.2.2.1 ground.2.2.2.2
  · intro x y z entry hz lower
    obtain ⟨hx, equal⟩ := (pair_mem_attachmentOldEmbeddingGraph P x y).1 entry
    subst y
    exact tile.old_graph_ideal hx hz lower
  · exact fun _ _ _ entry hz lower => tile.template_graph_ideal entry hz lower
  · exact tile.vertex_cover

theorem exists_compressionTileHeight {f : ZFSet.{u}}
    (embedding : MeetEmbeddingCode P P r r μ μ f)
    (K : {x : ZFSet.{u} // x ∈ P})
    (range : ∀ z, (∃ x ∈ P, ZFSet.pair x z ∈ f) ↔ z ∈ P ∧ ZFSet.pair z K.val ∈ r) :
    let topRaw : {x : ZFSet.{u} // x ∈ P} := ⟨SetMembers.raw top, SetMembers.raw_mem top⟩
    let rawGreatest : ∀ x, source.toMeetOrder.le x topRaw :=
      fun x => by
        change ZFSet.pair x.val (SetMembers.raw top) ∈ r
        have lower := greatest (SetMembers.ofMem x.val x.property)
        change ZFSet.pair (SetMembers.raw (SetMembers.ofMem x.val x.property)) (SetMembers.raw top) ∈ r at lower
        simpa only [SetMembers.raw_ofMem] using lower
    let tile := compressionTileCoding source embedding topRaw K rawGreatest range
    ∃ h ∈ M.sets, IntervalHeightCode tile.carrier tile.order D rD lo hi h ∧
      relationImage tile.carrier D h ∈ M.sets ∧
      M.groundEmbeddable (relationImage tile.carrier D h) ZFSet.omega := by
  dsimp only
  obtain ⟨h, ground, strict, inside, rangeGround, rangeSmall, _⟩ :=
    M.exists_groundHeightInterpolation pairing unions powers separation collection infinite
      hP hH hrH hOld hD hrD hc height linear target injection small hlo hhi gap
  have codes := compressionTile_exact_codes source embedding
    ⟨SetMembers.raw top, SetMembers.raw_mem top⟩ K
    (fun x => by
        change ZFSet.pair x.val (SetMembers.raw top) ∈ r
        have lower := greatest (SetMembers.ofMem x.val x.property)
        change ZFSet.pair (SetMembers.raw (SetMembers.ofMem x.val x.property)) (SetMembers.raw top) ∈ r at lower
        simpa only [SetMembers.raw_ofMem] using lower) range
  rw [codes.1, codes.2.1]
  exact ⟨h, ground, ⟨strict, inside⟩, rangeGround, rangeSmall⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
