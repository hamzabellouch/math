import OAI.SetTheory.PartitionPrinciple.Geometry.GroundExternalGenerators

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization
universe u

structure GroupEmbeddingCode (G H mG mH oneG oneH e : ZFSet.{u}) : Prop where
  injection : InjectionCode G H e
  one : ZFSet.pair oneG oneH ∈ e
  mul : ∀ a b c a' b' c', ZFSet.pair (ZFSet.pair a b) c ∈ mG →
    ZFSet.pair a a' ∈ e → ZFSet.pair b b' ∈ e → ZFSet.pair c c' ∈ e →
      ZFSet.pair (ZFSet.pair a' b') c' ∈ mH

namespace GroupEmbeddingCode

theorem identity {G m inv one : ZFSet.{u}} (group : GroupCode G m inv one) :
    GroupEmbeddingCode G G m m one one (identityFunctionGraph G) := by
  refine ⟨identityFunctionGraph_injection G,
    (pair_mem_identityFunctionGraph G one one).2 ⟨rfl, group.identity_mem⟩, ?_⟩
  intro a b c a' b' c' product first second third
  obtain ⟨rfl, _⟩ := (pair_mem_identityFunctionGraph G a a').1 first
  obtain ⟨rfl, _⟩ := (pair_mem_identityFunctionGraph G b b').1 second
  obtain ⟨rfl, _⟩ := (pair_mem_identityFunctionGraph G c c').1 third
  exact product

theorem compose {G H K mG mH mK oneG oneH oneK e f : ZFSet.{u}}
    (first : GroupEmbeddingCode G H mG mH oneG oneH e)
    (second : GroupEmbeddingCode H K mH mK oneH oneK f) :
    GroupEmbeddingCode G K mG mK oneG oneK (relationCompose G H K e f) := by
  refine ⟨first.injection.compose second.injection, ?_, ?_⟩
  · have oneG := (ZFSet.pair_mem_prod.1 (first.injection.function.1 first.one)).1
    have oneH := (ZFSet.pair_mem_prod.1 (first.injection.function.1 first.one)).2
    have oneK := (ZFSet.pair_mem_prod.1 (second.injection.function.1 second.one)).2
    exact (pair_mem_relationCompose _ _ _ _ _ _ _).2 ⟨oneG, oneK, _, oneH, first.one, second.one⟩
  · intro a b c a' b' c' product aa bb cc
    obtain ⟨_, _, x, _, ax, xa⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 aa
    obtain ⟨_, _, y, _, by', yb⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 bb
    obtain ⟨_, _, z, _, cz, zc⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 cc
    exact second.mul x y z a' b' c' (first.mul a b c x y z product ax by' cz) xa yb zc

theorem map_inv {G H mG mH invG invH oneG oneH e a b a' b' : ZFSet.{u}}
    (embedding : GroupEmbeddingCode G H mG mH oneG oneH e)
    (source : GroupCode G mG invG oneG) (target : GroupCode H mH invH oneH)
    (inverse : ZFSet.pair a b ∈ invG) (first : ZFSet.pair a a' ∈ e) (second : ZFSet.pair b b' ∈ e) :
    ZFSet.pair a' b' ∈ invH := by
  let := target.toGroup
  have bounds := ZFSet.pair_mem_prod.1 (source.inv_function.1 inverse)
  have product := embedding.mul b a oneG b' a' oneH
    (source.inv_mul a bounds.1 b bounds.2 inverse) second first embedding.one
  let x := SetMembers.ofMem a' (ZFSet.pair_mem_prod.1 (embedding.injection.function.1 first)).2
  let y := SetMembers.ofMem b' (ZFSet.pair_mem_prod.1 (embedding.injection.function.1 second)).2
  have product' : y * x = (1 : SetMembers H) := by
    apply (target.mul_eq_iff y x target.one).2
    simpa only [target.raw_one, x, y, SetMembers.raw_ofMem] using product
  have equal : x⁻¹ = y := inv_eq_of_mul_eq_one_left product'
  have entry := target.inv_mem x
  change ZFSet.pair (SetMembers.raw x) (SetMembers.raw (x⁻¹)) ∈ invH at entry
  rw [equal] at entry
  simpa only [x, y, SetMembers.raw_ofMem] using entry

end GroupEmbeddingCode
end PartitionPilot.Forcing

namespace PartitionPilot.SetRealization.Presentation
open Forcing
universe u
variable {G H : Type u} [Group G] [Group H]

theorem groupEmbeddingCode (s : Presentation G) (t : Presentation H)
    (f : G →* H) (injective : Function.Injective f) :
    GroupEmbeddingCode s.carrier t.carrier
      ((s.product s).graph s (fun p => p.1 * p.2))
      ((t.product t).graph t (fun p => p.1 * p.2)) (s.encode 1) (t.encode 1) (s.graph t f) := by
  refine ⟨s.graph_injection t f injective, (s.pair_mem_graph t f 1 1).2 f.map_one, ?_⟩
  intro a b c a' b' c' product first second third
  obtain ⟨a, aa⟩ := (s.mem_graph t f _).1 first
  obtain ⟨b, bb⟩ := (s.mem_graph t f _).1 second
  obtain ⟨c, cc⟩ := (s.mem_graph t f _).1 third
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 aa
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 bb
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 cc
  have mul := ((s.product s).pair_mem_graph s _ (a, b) c).1 product
  exact ((t.product t).pair_mem_graph t _ (f a, f b) (f c)).2 (by rw [← mul, f.map_mul])

end PartitionPilot.SetRealization.Presentation



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
open Compression.RecursiveMaps.CosetGeometry
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)

include pairing unions powers separation infinite in
theorem externalOldInclusion_groupEmbedding_of_presentation
    {J L : Type u} [Group J] (s : Presentation J) (t : Presentation L)
    (hG : s.carrier ∈ M.sets) (hS : t.carrier ∈ M.sets) :
    let m := (s.product s).graph s (fun p => p.1 * p.2)
    GroupEmbeddingCode s.carrier (M.externalGroupCarrier s.carrier t.carrier m (s.encode 1))
      m (M.externalGroupMultiplication s.carrier t.carrier m (s.encode 1))
      (s.encode 1) (M.externalGroupIdentity s.carrier t.carrier m (s.encode 1))
      (M.externalOldInclusion s.carrier t.carrier m (s.encode 1)) := by
  dsimp only
  rw [M.externalOldInclusion_eq_graph pairing unions powers separation infinite s t hG hS,
    M.externalGroupMultiplication_eq_graph pairing unions powers separation infinite s t hG hS,
    M.externalGroupIdentity_eq_encode pairing unions powers separation infinite s t hG hS]
  exact s.groupEmbeddingCode
    (M.externalGroupPresentation pairing unions powers separation infinite s t hG hS)
    (old J L) (old_injective J L)

include pairing unions powers separation infinite in
theorem externalOldInclusion_groupEmbedding {G S m inv one : ZFSet.{u}}
    (group : GroupCode G m inv one) (hG : G ∈ M.sets) (hS : S ∈ M.sets) :
    GroupEmbeddingCode G (M.externalGroupCarrier G S m one)
      m (M.externalGroupMultiplication G S m one) one (M.externalGroupIdentity G S m one)
      (M.externalOldInclusion G S m one) := by
  let := group.toGroup
  have code := M.externalOldInclusion_groupEmbedding_of_presentation pairing unions powers separation infinite
    (SetMembers.presentation G) (SetMembers.presentation S) hG hS
  dsimp only at code
  rw [group.multiplication_graph_eq, group.identity_code_eq] at code
  exact code

include pairing unions powers separation infinite in
theorem externalOldInclusion_ground_groupEmbedding {G S m inv one : ZFSet.{u}}
    (group : GroupCode G m inv one) (hG : G ∈ M.sets) (hS : S ∈ M.sets) (hm : m ∈ M.sets) :
    M.externalOldInclusion G S m one ∈ M.sets ∧
      GroupEmbeddingCode G (M.externalGroupCarrier G S m one)
        m (M.externalGroupMultiplication G S m one) one (M.externalGroupIdentity G S m one)
        (M.externalOldInclusion G S m one) :=
  ⟨(M.externalGeneratorGraphs_ground_injections pairing unions powers separation infinite group hG hS hm).1,
    M.externalOldInclusion_groupEmbedding pairing unions powers separation infinite group hG hS⟩

include pairing unions powers separation infinite in
theorem externalOldInclusion_preserves_inverse {G S m inv one a b a' b' : ZFSet.{u}}
    (group : GroupCode G m inv one) (hG : G ∈ M.sets) (hS : S ∈ M.sets)
    (inverse : ZFSet.pair a b ∈ inv)
    (first : ZFSet.pair a a' ∈ M.externalOldInclusion G S m one)
    (second : ZFSet.pair b b' ∈ M.externalOldInclusion G S m one) :
    ZFSet.pair a' b' ∈ M.externalGroupInverse G S m inv one :=
  (M.externalOldInclusion_groupEmbedding pairing unions powers separation infinite group hG hS).map_inv
    group (M.externalGroup_code pairing unions powers separation infinite group hG hS) inverse first second

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
