import OAI.SetTheory.PartitionPrinciple.Definability.CrossStageMembershipFormulas
import OAI.SetTheory.PartitionPrinciple.Definability.NameSupportFormulas

namespace OAI


namespace PartitionPilot.Forcing.Name
open SetRealization
universe u v
variable {P : Type u} {s : Presentation P}

theorem isName_of_subset {T z : ZFSet.{u}}
    (valid : ∀ x ∈ T, IsName s x) (subset : z ⊆ ZFSet.prod T s.carrier) :
    IsName s z := by
  refine IsName.mk ?_ ?_
  · intro w hw
    obtain ⟨x, _, y, hy, equal⟩ := ZFSet.mem_prod.1 (subset hw)
    obtain ⟨p, rfl⟩ := (s.mem_carrier y).1 hy
    exact ⟨x, p, equal⟩
  · intro x p entry
    exact valid x (ZFSet.pair_mem_prod.1 (subset entry)).1

def ofSubset {T z : ZFSet.{u}} (valid : ∀ x ∈ T, IsName s x)
    (subset : z ⊆ ZFSet.prod T s.carrier) : Name s :=
  ⟨z, isName_of_subset valid subset⟩

theorem ofSubset_code {T z : ZFSet.{u}} (valid : ∀ x ∈ T, IsName s x)
    (subset : z ⊆ ZFSet.prod T s.carrier) : (ofSubset valid subset).val = z := rfl

theorem entry_ofSubset {T z : ZFSet.{u}} (valid : ∀ x ∈ T, IsName s x)
    (subset : z ⊆ ZFSet.prod T s.carrier) (σ : Name s) (p : P) :
    Entry σ (ofSubset valid subset) p ↔ ZFSet.pair σ.val (s.encode p) ∈ z := Iff.rfl

theorem entry_term_of_subset {T : ZFSet.{u}} {σ τ : Name s} {p : P}
    (subset : τ.val ⊆ ZFSet.prod T s.carrier) (entry : Entry σ τ p) : σ.val ∈ T :=
  (ZFSet.pair_mem_prod.1 (subset entry)).1

theorem act_subset_of_closed {G : Type v} [Group G] [PartialOrder P]
    (a : PosetAction G P) {T : ZFSet.{u}}
    (closed : ∀ g (σ : Name s), σ.val ∈ T → (a.act s g σ).val ∈ T)
    {τ : Name s} (subset : τ.val ⊆ ZFSet.prod T s.carrier) (g : G) :
    (a.act s g τ).val ⊆ ZFSet.prod T s.carrier := by
  intro z hz
  obtain ⟨ν, p, rfl⟩ := entries_cover (a.act s g τ) hz
  change Entry ν (rename s (a.iso g) τ) p at hz
  obtain ⟨σ, q, entry, rfl, rfl⟩ := (entry_rename s (a.iso g) τ ν p).1 hz
  exact ZFSet.pair_mem_prod.2
    ⟨closed g σ (entry_term_of_subset subset entry), s.encode_mem _⟩

end PartitionPilot.Forcing.Name



namespace PartitionPilot.Forcing.Name
open SetRealization
universe u
variable {Upper Lower : Type u} [PartialOrder Upper]
variable (s : Presentation Upper) (t : Presentation Lower)
variable (inclusion : Lower → Upper) (J : ZFSet.{u}) (tau : Name s)

noncomputable def crossStageMembershipCode : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ sigma : Name t, ∃ p : Lower,
    z = ZFSet.pair sigma.val (t.encode p) ∧
      ForcesMem (inclusion p) (rename s inclusion sigma) tau)
    (ZFSet.prod J t.carrier)

theorem crossStageMembershipCode_subset :
    crossStageMembershipCode s t inclusion J tau ⊆ ZFSet.prod J t.carrier :=
  fun _ member => (ZFSet.mem_sep.1 member).1

theorem pair_mem_crossStageMembershipCode (sigma : Name t) (p : Lower) :
    ZFSet.pair sigma.val (t.encode p) ∈ crossStageMembershipCode s t inclusion J tau ↔
      sigma.val ∈ J ∧ ForcesMem (inclusion p) (rename s inclusion sigma) tau := by
  change (_ ∈ ZFSet.sep _ _) ↔ _
  rw [ZFSet.mem_sep]
  constructor
  · rintro ⟨bound, nu, q, equal, forced⟩
    obtain ⟨names, conditions⟩ := ZFSet.pair_inj.1 equal
    have sameName : sigma = nu := Subtype.ext names
    have sameCondition : p = q := t.injective conditions
    exact ⟨(ZFSet.pair_mem_prod.1 bound).1, sameName.symm ▸ sameCondition.symm ▸ forced⟩
  · rintro ⟨member, forced⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨member, t.encode_mem p⟩, sigma, p, rfl, forced⟩

theorem crossStageMembershipCode_isName (valid : ∀ z ∈ J, IsName t z) :
    IsName t (crossStageMembershipCode s t inclusion J tau) :=
  isName_of_subset valid (crossStageMembershipCode_subset s t inclusion J tau)

noncomputable def crossStageMembershipName (valid : ∀ z ∈ J, IsName t z)
    (tau : Name s) : Name t :=
  ⟨crossStageMembershipCode s t inclusion J tau,
    crossStageMembershipCode_isName s t inclusion J tau valid⟩

theorem crossStageMembershipName_val (valid : ∀ z ∈ J, IsName t z) :
    (crossStageMembershipName s t inclusion J valid tau).val =
      crossStageMembershipCode s t inclusion J tau := rfl

theorem entry_crossStageMembershipName (valid : ∀ z ∈ J, IsName t z)
    (sigma : Name t) (p : Lower) :
    Entry sigma (crossStageMembershipName s t inclusion J valid tau) p ↔
      sigma.val ∈ J ∧ ForcesMem (inclusion p) (rename s inclusion sigma) tau :=
  pair_mem_crossStageMembershipCode s t inclusion J tau sigma p

end PartitionPilot.Forcing.Name



namespace PartitionPilot.Forcing.SetFormula
open SetRealization
universe u
variable {P : Type u} [Preorder P] {s : Presentation P}

theorem forces_nonempty_iff_dense_activeTerms (D : Name.NameDomain s)
    (U : D.names) (T : ZFSet.{u})
    (shape : U.val.val ⊆ ZFSet.prod T s.carrier) (p : P) :
    Forces D (ex (.mem 0 1)) ![U] p ↔
      DenseBelow p {q | ∃ u : D.names, u.val.val ∈ T ∧ Name.ForcesMem q u.val U.val} := by
  rw [forces_ex_iff]
  constructor
  · intro dense r below
    obtain ⟨q, qr, z, member⟩ := dense r below
    change Name.ForcesMem q z.val U.val at member
    obtain ⟨v, vq, w, k, entry, vk, equal⟩ := member q le_rfl
    refine ⟨v, vq.trans qr, ⟨w, D.children U.property entry⟩,
      Name.entry_term_of_subset shape entry, ?_⟩
    exact Name.forcesMem_mono (Name.forcesMem_entry entry) vk
  · intro dense r below
    obtain ⟨q, qr, u, term, member⟩ := dense r below
    exact ⟨q, qr, u, member⟩

end PartitionPilot.Forcing.SetFormula



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {Upper Lower : Type u} [PartialOrder Upper]
variable (s : Presentation Upper) (t : Presentation Lower) (inclusion : Lower → Upper)
variable (unchanged : ∀ p, s.encode (inclusion p) = t.encode p)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0)
variable (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
variable (upperGround : s.carrier ∈ M.sets) (upperOrderGround : s.conditionOrder ∈ M.sets)
variable (lowerGround : t.carrier ∈ M.sets)
variable {J : ZFSet.{u}} (hJ : J ∈ M.sets) (valid : ∀ u ∈ J, IsName t u)
variable (tau : Name s) (hTau : tau.val ∈ M.sets)
include unchanged pairing unions powers separation collection upperGround upperOrderGround lowerGround hJ valid hTau

theorem crossStageMembershipCode_eq_selection :
    Name.crossStageMembershipCode s t inclusion J tau =
      ZFSet.sep (fun z => Realize M.sets (crossStageMembershipEntryFormula 0 1 2 3 4 5)
        (extend z ![J, t.carrier, s.carrier, s.conditionOrder, tau.val])) (ZFSet.prod J t.carrier) := by
  have productGround := M.prod_mem pairing unions powers separation hJ lowerGround
  have recognize (z : ZFSet.{u}) (hz : z ∈ M.sets) :
      Realize M.sets (crossStageMembershipEntryFormula 0 1 2 3 4 5)
        (extend z ![J, t.carrier, s.carrier, s.conditionOrder, tau.val]) ↔
      z ∈ Name.crossStageMembershipCode s t inclusion J tau := by
    rw [M.realize_crossStageMembershipEntryFormula s t inclusion unchanged
      pairing unions powers separation collection upperGround upperOrderGround lowerGround hJ valid tau hTau
      0 1 2 3 4 5 _ hz rfl rfl rfl rfl rfl]
    constructor
    · rintro ⟨sigma, member, p, rfl, forced⟩
      exact (Name.pair_mem_crossStageMembershipCode s t inclusion J tau sigma p).2 ⟨member, forced⟩
    · intro member
      obtain ⟨bound, sigma, p, rfl, forced⟩ := ZFSet.mem_sep.1 member
      exact ⟨sigma, (ZFSet.pair_mem_prod.1 bound).1, p, rfl, forced⟩
  apply ZFSet.ext
  intro z
  rw [ZFSet.mem_sep]
  constructor
  · intro member
    have bound := Name.crossStageMembershipCode_subset s t inclusion J tau member
    exact ⟨bound, (recognize z (M.transitive productGround bound)).2 member⟩
  · rintro ⟨bound, formula⟩
    exact (recognize z (M.transitive productGround bound)).1 formula

theorem crossStageMembershipCode_mem :
    Name.crossStageMembershipCode s t inclusion J tau ∈ M.sets := by
  rw [M.crossStageMembershipCode_eq_selection s t inclusion unchanged pairing unions powers
    separation collection upperGround upperOrderGround lowerGround hJ valid tau hTau]
  exact M.separation_mem separation (crossStageMembershipEntryFormula 0 1 2 3 4 5)
    ![J, t.carrier, s.carrier, s.conditionOrder, tau.val]
    (Fin.cases hJ (Fin.cases lowerGround (Fin.cases upperGround
      (Fin.cases upperOrderGround (Fin.cases hTau (fun i => Fin.elim0 i))))))
    (M.prod_mem pairing unions powers separation hJ lowerGround)

theorem crossStageMembershipName_mem :
    (Name.crossStageMembershipName s t inclusion J valid tau).val ∈ M.sets :=
  M.crossStageMembershipCode_mem s t inclusion unchanged pairing unions powers separation collection
    upperGround upperOrderGround lowerGround hJ valid tau hTau

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.PosetAction

open Compression.RecursiveMaps Compression.RecursiveMaps.CosetGeometry.OrderAction
universe u
variable {G I : Type u} [Group G] [PartialOrder I] (a : PosetAction G I)

theorem point_inv_left (g : G) (x : I) : a.iso g⁻¹ (a.iso g x) = x := by
  rw [← a.mul, inv_mul_cancel, a.one]

theorem point_inv_right (g : G) (x : I) : a.iso g (a.iso g⁻¹ x) = x := by
  rw [← a.mul, mul_inv_cancel, a.one]

def principalFix (C : I) : Subgroup G where
  carrier := {g | ∀ x, x ≤ C → a.iso g x = x}
  one_mem' := fun x _ => a.one x
  mul_mem' {g h} hg hh x lower := by rw [a.mul, hh x lower, hg x lower]
  inv_mem' {g} hg x lower := by
    apply (a.iso g).injective
    exact (a.point_inv_right g x).trans (hg x lower).symm

theorem principalFix_antitone {C D : I} (lower : C ≤ D) : a.principalFix D ≤ a.principalFix C :=
  fun _ fixed x hx => fixed x (le_trans hx lower)

theorem principalFix_conjugation (g h : G) (C : I) :
    conjugateHom g h ∈ a.principalFix (a.iso g C) ↔ h ∈ a.principalFix C := by
  constructor
  · intro fixed x lower
    apply (a.iso g).injective
    have eq := fixed (a.iso g x) ((a.iso g).monotone lower)
    change a.iso (g * h * g⁻¹) (a.iso g x) = a.iso g x at eq
    rw [a.mul, a.mul, a.point_inv_left] at eq
    exact eq
  · intro fixed x lower
    have old : a.iso g⁻¹ x ≤ C := by
      have back := (a.iso g⁻¹).monotone lower
      simpa only [a.point_inv_left] using back
    change a.iso (g * h * g⁻¹) x = x
    rw [a.mul, a.mul, fixed _ old, a.point_inv_right]

def PrincipalSupported (K : Subgroup G) : Prop := ∃ C, a.principalFix C ≤ K

theorem principalSupported_top (C : I) : a.PrincipalSupported ⊤ := ⟨C, le_top⟩

theorem principalSupported_upward {K H : Subgroup G}
    (supported : a.PrincipalSupported K) (lower : K ≤ H) : a.PrincipalSupported H := by
  obtain ⟨C, hc⟩ := supported
  exact ⟨C, le_trans hc lower⟩

theorem principalSupported_inf (directed : ∀ C D : I, ∃ E, C ≤ E ∧ D ≤ E)
    {K H : Subgroup G} (left : a.PrincipalSupported K) (right : a.PrincipalSupported H) :
    a.PrincipalSupported (K ⊓ H) := by
  obtain ⟨C, hc⟩ := left
  obtain ⟨D, hd⟩ := right
  obtain ⟨E, ce, de⟩ := directed C D
  exact ⟨E, le_inf (le_trans (a.principalFix_antitone ce) hc)
    (le_trans (a.principalFix_antitone de) hd)⟩

theorem principalSupported_conjugate (g : G) {K : Subgroup G} (supported : a.PrincipalSupported K) :
    a.PrincipalSupported (K.map (conjugateHom g)) := by
  obtain ⟨C, hc⟩ := supported
  refine ⟨a.iso g C, ?_⟩
  intro h fixed
  let k := g⁻¹ * h * g
  have eq : conjugateHom g k = h := by simp [conjugateHom, k, mul_assoc]
  have old : k ∈ a.principalFix C := (a.principalFix_conjugation g k C).1 (eq.symm ▸ fixed)
  exact Subgroup.mem_map.2 ⟨k, hc old, eq⟩

def principalSupportFamily (C : I) (directed : ∀ C D : I, ∃ E, C ≤ E ∧ D ≤ E) :
    NormalSubgroupFamily G where
  mem := a.PrincipalSupported
  top := a.principalSupported_top C
  upward := a.principalSupported_upward
  inf := a.principalSupported_inf directed
  conjugate := a.principalSupported_conjugate

theorem principalSupportFamily_basis (C : I) (directed : ∀ C D : I, ∃ E, C ≤ E ∧ D ≤ E)
    (H : Subgroup G) : (a.principalSupportFamily C directed).mem H ↔ ∃ D, a.principalFix D ≤ H := Iff.rfl

end PartitionPilot.Forcing.PosetAction



namespace PartitionPilot.Forcing.Name
open SetRealization Compression.RecursiveMaps
universe u v

theorem exists_commonPrincipalNameSupport {G L : Type u} [Group G] [PartialOrder L]
    {P : Type v} [PartialOrder P] (a : PosetAction G P) (s : Presentation P)
    (d : PosetAction G L) (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
    {n : Nat} (tau : Fin n → Name s)
    (symmetric : ∀ i, (d.principalSupportFamily base directed).mem (a.stabilizer s (tau i))) :
    ∃ C : L, base ≤ C ∧ ∀ i, d.principalFix C ≤ a.stabilizer s (tau i) := by
  have allSupported := (d.principalSupportFamily base directed).fin_iInf
    (fun i => a.stabilizer s (tau i)) symmetric
  obtain ⟨B, bound⟩ := (d.principalSupportFamily_basis base directed _).1 allSupported
  obtain ⟨C, hBase, hB⟩ := directed base B
  refine ⟨C, hBase, fun i => ?_⟩
  exact (d.principalFix_antitone hB).trans (bound.trans (iInf_le _ i))

end PartitionPilot.Forcing.Name



namespace PartitionPilot.Forcing
open SetRealization Compression.RecursiveMaps Compression.RecursiveMaps.CosetGeometry.OrderAction
universe u v
variable {P : Type u} [PartialOrder P] {G : Type v} [Group G]

def NiceNameCode (a : PosetAction G P) (s : Presentation P)
    (T : ZFSet.{u}) (K : Subgroup G) (z : ZFSet.{u}) : Prop :=
  ∃ τ : Name s, τ.val = z ∧ τ.val ⊆ ZFSet.prod T s.carrier ∧ K ≤ a.stabilizer s τ

variable (a : PosetAction G P) (s : Presentation P)

theorem niceNameCode_iff {T : ZFSet.{u}} {K : Subgroup G} (τ : Name s) :
    NiceNameCode a s T K τ.val ↔
      τ.val ⊆ ZFSet.prod T s.carrier ∧ K ≤ a.stabilizer s τ := by
  constructor
  · rintro ⟨ν, equal, subset, fixed⟩
    have same : ν = τ := Subtype.ext equal
    exact same ▸ ⟨subset, fixed⟩
  · rintro ⟨subset, fixed⟩
    exact ⟨τ, rfl, subset, fixed⟩

theorem niceNameCode_ofSubset_iff {T z : ZFSet.{u}} {K : Subgroup G}
    (valid : ∀ x ∈ T, IsName s x) (subset : z ⊆ ZFSet.prod T s.carrier) :
    NiceNameCode a s T K z ↔
      ∀ g ∈ K, a.act s g (Name.ofSubset valid subset) = Name.ofSubset valid subset := by
  change NiceNameCode a s T K (Name.ofSubset valid subset).val ↔ _
  rw [niceNameCode_iff]
  exact ⟨fun result => result.2, fun fixed => ⟨subset, fixed⟩⟩

theorem niceNameCode_isName {T z : ZFSet.{u}} {K : Subgroup G}
    (code : NiceNameCode a s T K z) : IsName s z := by
  obtain ⟨τ, equal, _, _⟩ := code
  exact equal ▸ τ.property

theorem niceNameCode_subset {T z : ZFSet.{u}} {K : Subgroup G}
    (code : NiceNameCode a s T K z) : z ⊆ ZFSet.prod T s.carrier := by
  obtain ⟨τ, equal, subset, _⟩ := code
  exact equal ▸ subset

theorem niceNameCode_hs (F : NormalSubgroupFamily G) {T : ZFSet.{u}} {K : Subgroup G}
    (member : F.mem K)
    (children : ∀ σ : Name s, σ.val ∈ T → HereditarilySymmetric a s F σ)
    {τ : Name s} (code : NiceNameCode a s T K τ.val) : HereditarilySymmetric a s F τ := by
  obtain ⟨subset, fixed⟩ := (niceNameCode_iff a s τ).1 code
  exact HereditarilySymmetric.mk (F.upward member fixed)
    (fun σ p entry => children σ (Name.entry_term_of_subset subset entry))

theorem niceNameCode_conjugate {T : ZFSet.{u}} {K : Subgroup G}
    (closed : ∀ g (σ : Name s), σ.val ∈ T → (a.act s g σ).val ∈ T)
    {τ : Name s} (code : NiceNameCode a s T K τ.val) (g : G) :
    NiceNameCode a s T (K.map (conjugateHom g)) (a.act s g τ).val := by
  obtain ⟨subset, fixed⟩ := (niceNameCode_iff a s τ).1 code
  apply (niceNameCode_iff a s _).2
  refine ⟨Name.act_subset_of_closed a closed subset g, ?_⟩
  intro h member
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 member
  change a.act s (g * k * g⁻¹) (a.act s g τ) = a.act s g τ
  rw [a.act_mul, a.act_mul, a.act_inv_left, fixed hk]

theorem niceNameCode_act_iff {T : ZFSet.{u}} {K : Subgroup G}
    (closed : ∀ g (σ : Name s), σ.val ∈ T → (a.act s g σ).val ∈ T)
    (g : G) (τ : Name s) :
    NiceNameCode a s T (K.map (conjugateHom g)) (a.act s g τ).val ↔
      NiceNameCode a s T K τ.val := by
  constructor
  · intro code
    obtain ⟨subset, fixed⟩ := (niceNameCode_iff a s _).1 code
    apply (niceNameCode_iff a s τ).2
    refine ⟨?_, ?_⟩
    · have back := Name.act_subset_of_closed a closed subset g⁻¹
      simpa only [a.act_inv_left] using back
    · intro k hk
      have image : conjugateHom g k ∈ K.map (conjugateHom g) :=
        Subgroup.mem_map.2 ⟨k, hk, rfl⟩
      have equal := fixed image
      change a.act s (g * k * g⁻¹) (a.act s g τ) = a.act s g τ at equal
      rw [a.act_mul, a.act_mul, a.act_inv_left] at equal
      exact (a.nameEquiv s g).injective equal
  · intro code
    exact niceNameCode_conjugate a s closed code g

variable {L : Type v} [PartialOrder L]

theorem principalFix_map_conjugate (d : PosetAction G L) (g : G) (v : L) :
    (d.principalFix v).map (conjugateHom g) = d.principalFix (d.iso g v) := by
  apply Subgroup.ext
  intro h
  constructor
  · intro member
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 member
    exact (d.principalFix_conjugation g k v).2 hk
  · intro fixed
    let k := g⁻¹ * h * g
    have equal : conjugateHom g k = h := by simp [conjugateHom, k, mul_assoc]
    exact Subgroup.mem_map.2
      ⟨k, (d.principalFix_conjugation g k v).1 (equal.symm ▸ fixed), equal⟩

theorem niceNameCode_principal_hs (d : PosetAction G L) (base v : L)
    (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z) {T : ZFSet.{u}}
    (children : ∀ σ : Name s, σ.val ∈ T →
      HereditarilySymmetric a s (d.principalSupportFamily base directed) σ)
    {τ : Name s} (code : NiceNameCode a s T (d.principalFix v) τ.val) :
    HereditarilySymmetric a s (d.principalSupportFamily base directed) τ :=
  niceNameCode_hs a s (d.principalSupportFamily base directed) ⟨v, le_refl _⟩ children code

theorem niceNameCode_principal_act_iff (d : PosetAction G L) {T : ZFSet.{u}}
    (closed : ∀ g (σ : Name s), σ.val ∈ T → (a.act s g σ).val ∈ T)
    (g : G) (v : L) (τ : Name s) :
    NiceNameCode a s T (d.principalFix (d.iso g v)) (a.act s g τ).val ↔
      NiceNameCode a s T (d.principalFix v) τ.val := by
  rw [← principalFix_map_conjugate d g v]
  exact niceNameCode_act_iff a s closed g τ

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P)

noncomputable def niceNameCandidates (T : ZFSet.{u}) (K : Subgroup G) : ZFSet.{u} :=
  ZFSet.sep (NiceNameCode a s T K) (M.groundRelations T s.carrier)

theorem mem_niceNameCandidates (T : ZFSet.{u}) (K : Subgroup G) (z : ZFSet.{u}) :
    z ∈ M.niceNameCandidates a s T K ↔ z ∈ M.sets ∧ NiceNameCode a s T K z := by
  rw [niceNameCandidates, ZFSet.mem_sep, M.mem_groundRelations]
  constructor
  · exact fun h => ⟨h.1.1, h.2⟩
  · rintro ⟨ground, τ, equal, subset, fixed⟩
    exact ⟨⟨ground, equal ▸ subset⟩, τ, equal, subset, fixed⟩

theorem name_mem_niceNameCandidates (T : ZFSet.{u}) (K : Subgroup G) (τ : Name s) :
    τ.val ∈ M.niceNameCandidates a s T K ↔
      τ.val ∈ M.sets ∧ τ.val ⊆ ZFSet.prod T s.carrier ∧ K ≤ a.stabilizer s τ := by
  rw [M.mem_niceNameCandidates]
  constructor
  · rintro ⟨ground, σ, equal, subset, fixed⟩
    have same : σ = τ := Subtype.ext equal
    subst σ
    exact ⟨ground, subset, fixed⟩
  · rintro ⟨ground, subset, fixed⟩
    exact ⟨ground, τ, rfl, subset, fixed⟩

theorem niceNameCandidates_subset (T : ZFSet.{u}) (K : Subgroup G) :
    M.niceNameCandidates a s T K ⊆ M.groundRelations T s.carrier := by
  intro z hz
  exact (ZFSet.mem_sep.1 hz).1

theorem niceNameCandidates_mem {I : Type u} (t : Presentation G) (b : Presentation I)
    (K : I → Subgroup G)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
    (supports : supportBasisCode b t K ∈ M.sets)
    (maps : a.conditionMapFamily s t ∈ M.sets)
    {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
    (i : I) (hi : b.encode i ∈ M.sets) :
    M.niceNameCandidates a s T (K i) ∈ M.sets := by
  let B := M.groundRelations T s.carrier
  have hB : B ∈ M.sets := M.groundRelations_mem pairing unions powers separation hT carrier
  let params := extend (b.encode i) (extend s.carrier (extend t.carrier
    (extend (supportBasisCode b t K) (extend (a.conditionMapFamily s t) Fin.elim0))))
  have selected := M.separation_mem separation nameSupportFormula params
    (Fin.cases hi (Fin.cases carrier (Fin.cases group (Fin.cases supports
      (Fin.cases maps (fun j => Fin.elim0 j)))))) hB
  have equal : ZFSet.sep (fun z => Realize M.sets nameSupportFormula (extend z params)) B =
      M.niceNameCandidates a s T (K i) := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, niceNameCandidates, ZFSet.mem_sep]
    apply and_congr_right
    intro hz
    have data := (M.mem_groundRelations T s.carrier z).1 hz
    let τ := Name.ofSubset valid data.2
    have fixed := M.realize_nameSupportFormula a s t b K pairing unions powers separation collection
      carrier group supports maps i hi τ data.1
    change Realize M.sets nameSupportFormula (extend τ.val params) ↔ NiceNameCode a s T (K i) τ.val
    rw [fixed]
    constructor
    · intro h
      exact ⟨τ, rfl, data.2, h⟩
    · rintro ⟨σ, eq, _, h⟩
      have same : σ = τ := Subtype.ext eq
      exact same ▸ h
  exact equal ▸ selected

end PartitionPilot.Forcing.TransitiveGround

end OAI
