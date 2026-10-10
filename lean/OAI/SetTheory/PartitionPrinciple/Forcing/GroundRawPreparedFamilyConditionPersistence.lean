import OAI.SetTheory.PartitionPrinciple.Geometry.GroundCertificateProfileImageFamilies

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P]
variable (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0)
variable (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
include pairing unions powers separation collection carrier order

theorem preparedCertificateCode_condition_mono
    (nodes nodeOrder meet N visibility top omega : ZFSet.{u})
    (graphGround : visibility ∈ M.sets)
    (graphNames : ∀ v V, ZFSet.pair v V ∈ visibility → v ∈ nodes → IsName s V)
    (namesGround : N ∈ M.sets) (validN : ∀ tau ∈ N, IsName s tau)
    (z : (M.nameDomain s).names) (F B f e names : ZFSet.{u})
    {p q : P} (qp : q ≤ p)
    (code : PreparedCertificateCode M s.carrier s.conditionOrder (s.encode p)
      nodes nodeOrder meet N visibility top omega z.val.val F B f e names) :
    PreparedCertificateCode M s.carrier s.conditionOrder (s.encode q)
      nodes nodeOrder meet N visibility top omega z.val.val F B f e names := by
  obtain ⟨filter, coinitial, nonempty, enumerated, supported, forced⟩ := code
  refine ⟨filter, coinitial, nonempty, enumerated, supported, ?_⟩
  apply M.preparationForcingCode_condition_mono s pairing unions powers separation collection
    carrier order nodes N visibility graphGround graphNames namesGround validN z F f _ qp forced
  intro entry member
  obtain ⟨v, hv, tau, htau, rfl⟩ := ZFSet.mem_prod.1 (enumerated.1.1 member)
  have incidence := (pair_mem_visibilitySupportIncidence nodes N visibility top v tau).1
    (supported v tau member)
  exact ZFSet.pair_mem_prod.2 ⟨incidence.1, htau⟩

theorem preparedCertificateFamilyCode_condition_mono
    (nodes nodeOrder meet N visibility top omega J C E k enumerations : ZFSet.{u})
    (graphGround : visibility ∈ M.sets)
    (graphNames : ∀ v V, ZFSet.pair v V ∈ visibility → v ∈ nodes → IsName s V)
    (namesGround : N ∈ M.sets) (validN : ∀ tau ∈ N, IsName s tau)
    (requestsGround : J ∈ M.sets) (validJ : ∀ z ∈ J, IsName s z)
    {p q : P} (qp : q ≤ p)
    (code : PreparedCertificateFamilyCode M s.carrier s.conditionOrder (s.encode p)
      nodes nodeOrder meet N visibility top omega J C E k enumerations) :
    PreparedCertificateFamilyCode M s.carrier s.conditionOrder (s.encode q)
      nodes nodeOrder meet N visibility top omega J C E k enumerations := by
  refine ⟨code.1, code.2.1, ?_⟩
  intro z F B f e names stored enumerated
  have member := (ZFSet.pair_mem_prod.1 (code.1.1 stored)).1
  let name : (M.nameDomain s).names :=
    ⟨⟨z, validJ z member⟩, M.transitive requestsGround member⟩
  exact M.preparedCertificateCode_condition_mono s pairing unions powers separation collection
    carrier order nodes nodeOrder meet N visibility top omega graphGround graphNames
    namesGround validN name F B f e names qp (code.2.2 z F B f e names stored enumerated)

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u})

theorem preparedCertificateFamilyCode_raw_condition_mono
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (P order nodes nodeOrder meet N visibility top omega J C E k enumerations : ZFSet.{u})
    (orderCode : PartialOrderCode P order)
    (carrierGround : P ∈ M.sets) (orderGround : order ∈ M.sets)
    (graphGround : visibility ∈ M.sets)
    (graphNames : ∀ v V, ZFSet.pair v V ∈ visibility → v ∈ nodes →
      IsName (SetMembers.presentation P) V)
    (namesGround : N ∈ M.sets)
    (validN : ∀ tau ∈ N, IsName (SetMembers.presentation P) tau)
    (requestsGround : J ∈ M.sets)
    (validJ : ∀ z ∈ J, IsName (SetMembers.presentation P) z)
    (p q : ZFSet.{u}) (hp : p ∈ P) (hq : q ∈ P) (qp : ZFSet.pair q p ∈ order)
    (code : PreparedCertificateFamilyCode M P order p
      nodes nodeOrder meet N visibility top omega J C E k enumerations) :
    PreparedCertificateFamilyCode M P order q
      nodes nodeOrder meet N visibility top omega J C E k enumerations := by
  let := orderCode.toPartialOrder
  let s := SetMembers.presentation P
  have groundOrder : s.conditionOrder ∈ M.sets := M.decoded_order_mem orderCode orderGround
  have orderEq : s.conditionOrder = order := orderCode.conditionOrder_eq
  have pCode : s.encode (SetMembers.ofMem p hp) = p := SetMembers.raw_ofMem p hp
  have qCode : s.encode (SetMembers.ofMem q hq) = q := SetMembers.raw_ofMem q hq
  have typedBelow : SetMembers.ofMem q hq ≤ SetMembers.ofMem p hp := by
    change ZFSet.pair (SetMembers.raw (SetMembers.ofMem q hq))
      (SetMembers.raw (SetMembers.ofMem p hp)) ∈ order
    simpa only [SetMembers.raw_ofMem] using qp
  have initial : PreparedCertificateFamilyCode M s.carrier s.conditionOrder
      (s.encode (SetMembers.ofMem p hp)) nodes nodeOrder meet N visibility top omega
      J C E k enumerations := by
    exact (congrArg₂ (fun r c => PreparedCertificateFamilyCode M P r c
      nodes nodeOrder meet N visibility top omega J C E k enumerations) orderEq pCode).mpr code
  have moved := M.preparedCertificateFamilyCode_condition_mono s pairing unions powers
    separation collection carrierGround groundOrder nodes nodeOrder meet N visibility top omega
    J C E k enumerations graphGround graphNames namesGround validN requestsGround validJ
    typedBelow initial
  exact (congrArg₂ (fun r c => PreparedCertificateFamilyCode M P r c
    nodes nodeOrder meet N visibility top omega J C E k enumerations) orderEq qCode).mp moved

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
