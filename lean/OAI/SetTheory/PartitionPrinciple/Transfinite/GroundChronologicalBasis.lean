import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundCoinitialOperations

namespace OAI

section

namespace PartitionPilot.Forcing

universe u

noncomputable def birthEssentialSet (F T r birth : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun x => ∀ y ∈ F, ∀ a ∈ T, ∀ b ∈ T,
    ZFSet.pair y x ∈ r → ZFSet.pair y a ∈ birth → ZFSet.pair x b ∈ birth → a ∉ b) F

theorem mem_birthEssentialSet (F T r birth x : ZFSet.{u}) :
    x ∈ birthEssentialSet F T r birth ↔ x ∈ F ∧
      ∀ y ∈ F, ∀ a ∈ T, ∀ b ∈ T,
        ZFSet.pair y x ∈ r → ZFSet.pair y a ∈ birth → ZFSet.pair x b ∈ birth → a ∉ b :=
  ZFSet.mem_sep

theorem birthEssentialSet_subset (F T r birth : ZFSet.{u}) :
    birthEssentialSet F T r birth ⊆ F := fun _ hx => (ZFSet.mem_sep.1 hx).1

noncomputable def essentialBirthIndices (F T r birth : ZFSet.{u}) : ZFSet.{u} :=
  relationImage (birthEssentialSet F T r birth) T birth

theorem mem_essentialBirthIndices (F T r birth t : ZFSet.{u}) :
    t ∈ essentialBirthIndices F T r birth ↔ t ∈ T ∧
      ∃ x ∈ birthEssentialSet F T r birth, ZFSet.pair x t ∈ birth :=
  mem_relationImage _ _ _ _

theorem positive_above_birthEssential {L F T r birth : ZFSet.{u}}
    (subset : F ⊆ L) (born : ZFSet.IsFunc L T birth)
    (refl : ∀ x ∈ L, ZFSet.pair x x ∈ r)
    (trans : ∀ x ∈ L, ∀ y ∈ L, ∀ z ∈ L,
      ZFSet.pair x y ∈ r → ZFSet.pair y z ∈ r → ZFSet.pair x z ∈ r)
    {x : ZFSet.{u}} (positive : x ∈ F) :
    ∃ y ∈ birthEssentialSet F T r birth, ZFSet.pair y x ∈ r := by
  let S : Set ZFSet.{u} := {t | ∃ y ∈ F, ZFSet.pair y x ∈ r ∧ ZFSet.pair y t ∈ birth}
  obtain ⟨t, xt, _⟩ := born.2 x (subset positive)
  have inhabited : S.Nonempty := ⟨t, x, positive, refl x (subset positive), xt⟩
  obtain ⟨t, ⟨y, hy, below, yt⟩, minimal⟩ := ZFSet.mem_wf.has_min S inhabited
  refine ⟨y, (mem_birthEssentialSet F T r birth y).2 ⟨hy, ?_⟩, below⟩
  intro z hz a _ b _ zy za yb earlier
  obtain ⟨_, _, unique⟩ := born.2 y (subset hy)
  have eq : b = t := (unique b yb).trans (unique t yt).symm
  have aS : a ∈ S := ⟨z, hz, trans z (subset hz) y (subset hy) x (subset positive) zy below, za⟩
  exact minimal a aS (eq ▸ earlier)

namespace BoundedFormula

open SetFormula

def birthEssentialFormula {n} (x f t r birth : Fin n) : BoundedFormula n :=
  .allMem f (.allMem t.succ (.allMem t.succ.succ
    (imp (.conj (pairMembershipFormula 2 x.succ.succ.succ r.succ.succ.succ)
      (.conj (pairMembershipFormula 2 1 birth.succ.succ.succ)
        (pairMembershipFormula x.succ.succ.succ 0 birth.succ.succ.succ))) (.neg (.mem 1 0)))))

theorem truth_birthEssentialFormula {n} (x f t r birth : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (birthEssentialFormula x f t r birth) env ↔
      ∀ y ∈ env f, ∀ a ∈ env t, ∀ b ∈ env t,
        ZFSet.pair y (env x) ∈ env r → ZFSet.pair y a ∈ env birth →
          ZFSet.pair (env x) b ∈ env birth → a ∉ b := by
  simp only [birthEssentialFormula, Truth, truth_imp, truth_pairMembershipFormula]
  change (∀ y ∈ env f, ∀ a ∈ env t, ∀ b ∈ env t,
    ZFSet.pair y (env x) ∈ env r ∧ ZFSet.pair y a ∈ env birth ∧
      ZFSet.pair (env x) b ∈ env birth → a ∉ b) ↔ _
  constructor
  · intro h y hy a ha b hb below bornY bornX
    exact h y hy a ha b hb ⟨below, bornY, bornX⟩
  · intro h y hy a ha b hb premises
    exact h y hy a ha b hb premises.1 premises.2.1 premises.2.2

end BoundedFormula

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem birthEssentialSet_mem (separation : SeparationSchema M.sets)
    {F T r birth : ZFSet.{u}} (hF : F ∈ M.sets) (hT : T ∈ M.sets)
    (hr : r ∈ M.sets) (hBirth : birth ∈ M.sets) :
    birthEssentialSet F T r birth ∈ M.sets := by
  let params := extend F (extend T (extend r (extend birth Fin.elim0)))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.birthEssentialFormula 0 1 2 3 4) params
    (Fin.cases hF (Fin.cases hT (Fin.cases hr (Fin.cases hBirth (fun j => Fin.elim0 j))))) hF
  have eq : ZFSet.sep (fun x => BoundedFormula.Truth
      (BoundedFormula.birthEssentialFormula 0 1 2 3 4) (extend x params)) F =
      birthEssentialSet F T r birth := by
    apply ZFSet.ext
    intro x
    rw [ZFSet.mem_sep, mem_birthEssentialSet]
    exact and_congr Iff.rfl (BoundedFormula.truth_birthEssentialFormula 0 1 2 3 4 _)
  exact eq ▸ selected

theorem essentialBirthIndices_mem (separation : SeparationSchema M.sets)
    {F T r birth : ZFSet.{u}} (hF : F ∈ M.sets) (hT : T ∈ M.sets)
    (hr : r ∈ M.sets) (hBirth : birth ∈ M.sets) :
    essentialBirthIndices F T r birth ∈ M.sets :=
  M.relationImage_mem separation (M.birthEssentialSet_mem separation hF hT hr hBirth) hT hBirth

theorem exists_essentialBirthRepresentatives
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {F T r birth : ZFSet.{u}} (hF : F ∈ M.sets) (hT : T ∈ M.sets)
    (hr : r ∈ M.sets) (hBirth : birth ∈ M.sets) :
    ∃ g ∈ M.sets,
      ZFSet.IsFunc (essentialBirthIndices F T r birth) (birthEssentialSet F T r birth) g ∧
      g ⊆ relationConverse (birthEssentialSet F T r birth) (essentialBirthIndices F T r birth) birth ∧
      ∀ t ∈ essentialBirthIndices F T r birth,
        ∃ x ∈ birthEssentialSet F T r birth, ZFSet.pair t x ∈ g ∧ ZFSet.pair x t ∈ birth := by
  let E := birthEssentialSet F T r birth
  let S := essentialBirthIndices F T r birth
  have hE : E ∈ M.sets := M.birthEssentialSet_mem separation hF hT hr hBirth
  have hS : S ∈ M.sets := M.essentialBirthIndices_mem separation hF hT hr hBirth
  have hConverse := M.relationConverse_mem pairing unions powers separation hE hS hBirth
  have total : ∀ t ∈ S, ∃ x ∈ E, ZFSet.pair t x ∈ relationConverse E S birth := by
    intro t ht
    obtain ⟨_, x, hx, born⟩ := (mem_essentialBirthIndices F T r birth t).1 ht
    exact ⟨x, hx, (pair_mem_relationConverse E S birth x t).2 ⟨hx, ht, born⟩⟩
  obtain ⟨g, hg, function, restricted⟩ :=
    M.uniformize_relation pairing unions powers separation choice hS hE hConverse total
  refine ⟨g, hg, function, restricted, ?_⟩
  intro t ht
  obtain ⟨x, chosen, _⟩ := function.2 t ht
  have spec := (pair_mem_relationConverse E S birth x t).1 (restricted chosen)
  exact ⟨x, spec.1, chosen, spec.2.2⟩

theorem exists_essentialBirthInjectionRepresentatives
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {L F T r birth : ZFSet.{u}} (hF : F ∈ M.sets) (hT : T ∈ M.sets)
    (hr : r ∈ M.sets) (hBirth : birth ∈ M.sets)
    (subset : F ⊆ L) (born : ZFSet.IsFunc L T birth) :
    ∃ g ∈ M.sets,
      InjectionCode (essentialBirthIndices F T r birth) (birthEssentialSet F T r birth) g ∧
      g ⊆ relationConverse (birthEssentialSet F T r birth) (essentialBirthIndices F T r birth) birth := by
  obtain ⟨g, hg, function, restricted, _⟩ :=
    M.exists_essentialBirthRepresentatives pairing unions powers separation choice hF hT hr hBirth
  refine ⟨g, hg, ⟨function, ?_⟩, restricted⟩
  intro t v x tx vx
  have first := (pair_mem_relationConverse _ _ birth x t).1 (restricted tx)
  have second := (pair_mem_relationConverse _ _ birth x v).1 (restricted vx)
  obtain ⟨_, _, unique⟩ := born.2 x (subset (birthEssentialSet_subset F T r birth first.1))
  exact (unique t first.2.2).trans (unique v second.2.2).symm

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem internal_countable_basis_of_birth_layers
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {L F T r birth : ZFSet.{u}} (hF : F ∈ M.sets) (hT : T ∈ M.sets)
    (hr : r ∈ M.sets) (hBirth : birth ∈ M.sets)
    (order : PartialOrderCode L r) (subset : F ⊆ L) (born : ZFSet.IsFunc L T birth)
    (small : M.groundEmbeddable (essentialBirthIndices F T r birth) ZFSet.omega)
    (localBases : ∀ t ∈ essentialBirthIndices F T r birth,
      M.InternalCountableBelow r F (relationFiber (birthEssentialSet F T r birth)
        (relationConverse (birthEssentialSet F T r birth) (essentialBirthIndices F T r birth) birth) t)) :
    M.InternalCountableBelow r F F := by
  let E := birthEssentialSet F T r birth
  let S := essentialBirthIndices F T r birth
  let parts := relationConverse E S birth
  have hE : E ∈ M.sets := M.birthEssentialSet_mem separation hF hT hr hBirth
  have hS : S ∈ M.sets := M.essentialBirthIndices_mem separation hF hT hr hBirth
  have hParts : parts ∈ M.sets := M.relationConverse_mem pairing unions powers separation hE hS hBirth
  have cover (x : ZFSet.{u}) (hx : x ∈ E) : ∃ t ∈ S, ZFSet.pair t x ∈ parts := by
    obtain ⟨t, xt, _⟩ := born.2 x (subset (birthEssentialSet_subset F T r birth hx))
    have htT := (ZFSet.pair_mem_prod.1 (born.1 xt)).2
    have htS : t ∈ S := (mem_essentialBirthIndices F T r birth t).2 ⟨htT, x, hx, xt⟩
    exact ⟨t, htS, (pair_mem_relationConverse E S birth x t).2 ⟨hx, htS, xt⟩⟩
  obtain ⟨B, hB, smallB, positive, below⟩ := M.internalCountableBelow_indexed_union
    pairing unions powers separation infinite choice hS hr hF hE hParts small cover localBases
  refine ⟨B, hB, smallB, positive, ?_⟩
  intro x hx
  obtain ⟨y, hy, yx⟩ := positive_above_birthEssential subset born order.refl order.trans hx
  obtain ⟨b, hb, byLower⟩ := below y hy
  exact ⟨b, hb, order.trans b (subset (positive hb)) y
    (subset (birthEssentialSet_subset F T r birth hy)) x (subset hx) byLower yx⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
