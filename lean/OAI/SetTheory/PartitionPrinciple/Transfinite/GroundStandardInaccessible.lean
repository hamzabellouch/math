import OAI.SetTheory.PartitionPrinciple.Forcing.GroundInaccessibleConditions
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundCantorDiagonal
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundOmegaOneRowModel
import OAI.SetTheory.PartitionPrinciple.Models.GroundChoiceEnumerationTraces
import OAI.SetTheory.PartitionPrinciple.Models.GroundSupportedEqualityChoices

namespace OAI


namespace PartitionPilot.Forcing
open SetFormula
universe u

theorem InjectionCode.retarget {A B C f : ZFSet.{u}} (code : InjectionCode A B f)
    (subset : B ⊆ C) : InjectionCode A C f := by
  refine ⟨⟨?_, code.function.2⟩, code.injective⟩
  intro z entry
  obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 (code.function.1 entry)
  exact ZFSet.pair_mem_prod.2 ⟨hx, subset hy⟩

theorem TransitiveGround.groundEmbeddable_retarget {M : TransitiveGround.{u}} {A B C : ZFSet.{u}}
    (small : M.groundEmbeddable A B) (subset : B ⊆ C) : M.groundEmbeddable A C := by
  obtain ⟨f, hf, code⟩ := small
  exact ⟨f, hf, code.retarget subset⟩

theorem ordinalSetProperty_pair_bound {K α β : ZFSet.{u}}
    (ordinal : ordinalSetProperty K) (hα : α ∈ K) (hβ : β ∈ K) :
    ∃ γ ∈ K, α ⊆ γ ∧ β ⊆ γ := by
  rcases ordinalSetProperty_mem_compare ordinal hα hβ with lower | rfl | greater
  · exact ⟨β, hβ, fun x hx => ordinal.2 β hβ α lower x hx, fun _ hx => hx⟩
  · exact ⟨α, hα, fun _ hx => hx, fun _ hx => hx⟩
  · exact ⟨α, hα, fun _ hx => hx, fun x hx => ordinal.2 α hα β greater x hx⟩

namespace GroundBelow
variable {M : TransitiveGround.{u}} {A B K : ZFSet.{u}}

theorem common_bound (first : GroundBelow M A K) (second : GroundBelow M B K)
    (ordinal : ordinalSetProperty K) :
    ∃ γ ∈ K, M.groundEmbeddable A γ ∧ M.groundEmbeddable B γ := by
  obtain ⟨α, hα, first⟩ := first
  obtain ⟨β, hβ, second⟩ := second
  obtain ⟨γ, hγ, left, right⟩ := ordinalSetProperty_pair_bound ordinal hα hβ
  exact ⟨γ, hγ, TransitiveGround.groundEmbeddable_retarget first left, TransitiveGround.groundEmbeddable_retarget second right⟩

theorem of_member
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hK : K ∈ M.sets) (hA : A ∈ K) : GroundBelow M A K :=
  ⟨A, hA, identityFunctionGraph A,
    M.identityFunctionGraph_mem pairing unions powers separation (M.transitive hK hA),
    identityFunctionGraph_injection A⟩

end GroundBelow

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

namespace GroundCardinal
variable {M : TransitiveGround.{u}} {κ η : ZFSet.{u}}

theorem subset_of_embeddable (cardinal : GroundCardinal M κ)
    (ordinal : ordinalSetProperty η) (embedding : M.groundEmbeddable κ η) : κ ⊆ η := by
  obtain ⟨a, eqA⟩ := (ordinalSetProperty_iff κ).1 cardinal.1
  obtain ⟨b, eqB⟩ := (ordinalSetProperty_iff η).1 ordinal
  by_cases lower : b < a
  · have member : η ∈ κ := by rw [eqA, eqB, mem_ordinalCode_iff]; exact lower
    exact False.elim (cardinal.2 η member embedding)
  · rw [eqA, eqB, ordinalCode_subset_iff]
    exact le_of_not_gt lower

theorem embeddable_iff_subset (cardinal : GroundCardinal M κ)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hκ : κ ∈ M.sets) (ordinal : ordinalSetProperty η) :
    M.groundEmbeddable κ η ↔ κ ⊆ η := by
  refine ⟨cardinal.subset_of_embeddable ordinal, fun subset => ?_⟩
  exact ⟨identityFunctionGraph κ, M.identityFunctionGraph_mem pairing unions powers separation hκ,
    (identityFunctionGraph_injection κ).retarget subset⟩

theorem eq_of_mutual (first : GroundCardinal M κ) (second : GroundCardinal M η)
    (forward : M.groundEmbeddable κ η) (backward : M.groundEmbeddable η κ) : κ = η :=
  ZFSet.ext fun _ => ⟨fun hx => first.subset_of_embeddable second.1 forward hx,
    fun hx => second.subset_of_embeddable first.1 backward hx⟩

end GroundCardinal

theorem groundCardinal_iff_no_smaller_mutual
    (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {κ : ZFSet.{u}} (hκ : κ ∈ M.sets) :
    GroundCardinal M κ ↔ ordinalSetProperty κ ∧ ∀ β ∈ κ,
      ¬ (M.groundEmbeddable κ β ∧ M.groundEmbeddable β κ) := by
  constructor
  · exact fun h => ⟨h.1, fun β hβ both => h.2 β hβ both.1⟩
  · rintro ⟨ordinal, minimal⟩
    refine ⟨ordinal, fun β hβ forward => minimal β hβ ⟨forward, ?_⟩⟩
    exact ⟨identityFunctionGraph β,
      M.identityFunctionGraph_mem pairing unions powers separation (M.transitive hκ hβ),
      (identityFunctionGraph_injection β).retarget (fun x hx => ordinal.1 β hβ x hx)⟩

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
universe u

namespace GroundRegular
variable {M : TransitiveGround.{u}} {K : ZFSet.{u}}

theorem cofinal_regular (regular : GroundRegular M K) : GroundCofinalRegular M K := by
  intro α hα f hf cofinal
  obtain ⟨δ, hδ, bounded⟩ := regular α hα f hf cofinal.1
  obtain ⟨x, _, y, _, entry, comparison⟩ := cofinal.2 δ hδ
  have lower := bounded x y entry
  rcases comparison with rfl | above
  · exact ZFSet.mem_irrefl _ lower
  · exact ZFSet.mem_asymm lower above

end GroundRegular

namespace GroundCofinalRegular
variable {M : TransitiveGround.{u}} {K : ZFSet.{u}}

theorem regular (cofinalRegular : GroundCofinalRegular M K) (ordinal : ordinalSetProperty K) :
    GroundRegular M K := by
  classical
  intro α hα f hf function
  have missing : ∃ δ ∈ K, ¬ ∃ x ∈ α, ∃ y ∈ K,
      ZFSet.pair x y ∈ f ∧ (δ = y ∨ δ ∈ y) := by
    by_contra noMissing
    apply cofinalRegular α hα f hf
    refine ⟨function, ?_⟩
    intro β hβ
    by_contra gap
    exact noMissing ⟨β, hβ, gap⟩
  obtain ⟨δ, hδ, gap⟩ := missing
  refine ⟨δ, hδ, ?_⟩
  intro x y entry
  obtain ⟨hx, hy⟩ := ZFSet.pair_mem_prod.1 (function.1 entry)
  rcases ordinalSetProperty_mem_compare ordinal hδ hy with above | equal | below
  · exact False.elim (gap ⟨x, hx, y, hy, entry, Or.inr above⟩)
  · exact False.elim (gap ⟨x, hx, y, hy, entry, Or.inl equal⟩)
  · exact below

theorem iff_regular (ordinal : ordinalSetProperty K) :
    GroundCofinalRegular M K ↔ GroundRegular M K :=
  ⟨fun regularity => regularity.regular ordinal, GroundRegular.cofinal_regular⟩

end GroundCofinalRegular

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem exists_groundCardinalRepresentative {α : ZFSet.{u}}
    (hα : α ∈ M.sets) (ordinal : ordinalSetProperty α) :
    ∃ κ ∈ M.sets, GroundCardinal M κ ∧ (κ = α ∨ κ ∈ α) ∧
      ∃ f ∈ M.sets, InjectionCode α κ f ∧
        identityFunctionGraph κ ∈ M.sets ∧ InjectionCode κ α (identityFunctionGraph κ) := by
  classical
  let candidates : Set ZFSet.{u} := {κ | (κ = α ∨ κ ∈ α) ∧ M.groundEmbeddable α κ}
  have present : candidates.Nonempty := ⟨α, Or.inl rfl, identityFunctionGraph α,
    M.identityFunctionGraph_mem pairing unions powers separation hα,
    identityFunctionGraph_injection α⟩
  obtain ⟨κ, member, minimal⟩ := ZFSet.mem_wf.has_min candidates present
  have bound : κ = α ∨ κ ∈ α := member.1
  have hκ : κ ∈ M.sets := bound.elim (fun equal => equal ▸ hα) (M.transitive hα)
  have ordκ : ordinalSetProperty κ := bound.elim (fun equal => equal ▸ ordinal)
    (ordinalSetProperty_member ordinal)
  have subset : κ ⊆ α := bound.elim (fun equal => equal ▸ (fun _ hx => hx))
    (fun smaller x hx => ordinal.1 κ smaller x hx)
  obtain ⟨f, hf, forward⟩ := member.2
  have cardinal : GroundCardinal M κ := by
    refine ⟨ordκ, fun β hβ smaller => ?_⟩
    obtain ⟨g, hg, injection⟩ := smaller
    have hβM := M.transitive hκ hβ
    have candidate : β ∈ candidates := ⟨Or.inr (subset hβ),
      relationCompose α κ β f g,
      M.relationCompose_mem pairing unions powers separation hα hκ hβM hf hg,
      forward.compose injection⟩
    exact minimal β candidate hβ
  exact ⟨κ, hκ, cardinal, bound, f, hf, forward,
    M.identityFunctionGraph_mem pairing unions powers separation hκ,
    (identityFunctionGraph_injection κ).retarget subset⟩

theorem groundCardinalRepresentative_least {α κ : ZFSet.{u}}
    (hα : α ∈ M.sets) (hκ : κ ∈ M.sets)
    (cardinal : GroundCardinal M κ) (backward : M.groundEmbeddable κ α)
    {β : ZFSet.{u}} (hβ : β ∈ M.sets) (ordinal : ordinalSetProperty β)
    (forward : M.groundEmbeddable α β) : κ ⊆ β := by
  obtain ⟨f, hf, first⟩ := backward
  obtain ⟨g, hg, second⟩ := forward
  exact cardinal.subset_of_embeddable ordinal
    ⟨relationCompose κ α β f g,
      M.relationCompose_mem pairing unions powers separation hκ hα hβ hf hg,
      first.compose second⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem ordinalRelation_embeds
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {A K e : ZFSet.{u}} (hA : A ∈ M.sets) (hK : K ∈ M.sets) (he : e ∈ M.sets)
    (cardinal : GroundCardinal M K)
    (covers : ∀ x ∈ A, ∃ beta ∈ K, ZFSet.pair beta x ∈ e)
    (initial : ∀ beta ∈ K, GroundBelow M (relationImage (insert beta beta) A e) K) :
    M.groundEmbeddable A K := by
  classical
  obtain ⟨c, hc, chooser, least⟩ := M.exists_ordinalRelationChoice pairing unions powers separation
    choice hA hK he cardinal.1 covers
  obtain ⟨f, hf, trace⟩ := M.exists_choiceEnumerationTrace pairing unions powers separation collection
    hA hc hK cardinal.1 chooser
  have onto : ∀ x ∈ A, ∃ a ∈ K, ZFSet.pair a x ∈ f := by
    intro x hx
    by_contra missing
    obtain ⟨beta, hBeta, betaX⟩ := covers x hx
    have unused : ∀ a ∈ K, (enumerationRemainder A a (graphRestriction a f)).Nonempty := by
      intro a ha
      refine ⟨x, (mem_enumerationRemainder _ _ _ _).2 ⟨hx, ?_⟩⟩
      rintro ⟨b, hb, entry⟩
      exact missing ⟨b, cardinal.1.1 a ha b hb, (pair_mem_graphRestriction.1 entry).1⟩
    have injection := choiceEnumerationTrace_injection chooser cardinal.1 trace unused
    have bounded : InjectionCode K (relationImage (insert beta beta) A e) f := by
      refine ⟨⟨?_, injection.function.2⟩, injection.injective⟩
      intro z hz
      obtain ⟨a, ha, y, hy, rfl⟩ := ZFSet.mem_prod.1 (injection.function.1 hz)
      have step := trace.2 a ha y hz
      rcases step with ⟨R, _hR, rfl, selected⟩ | ⟨empty, _⟩
      · obtain ⟨i, hi, entry, minimal⟩ := least _ y selected
        have ix : i ∈ insert beta beta := by
          rcases ordinalSetProperty_mem_compare cardinal.1 hi hBeta with before | equal | after
          · exact ZFSet.mem_insert_of_mem beta before
          · exact equal ▸ ZFSet.mem_insert beta beta
          · apply False.elim
            apply minimal beta after x
            · apply (mem_enumerationRemainder _ _ _ _).2
              refine ⟨hx, ?_⟩
              rintro ⟨b, hb, bx⟩
              exact missing ⟨b, cardinal.1.1 a ha b hb, (pair_mem_graphRestriction.1 bx).1⟩
            · exact betaX
        exact ZFSet.pair_mem_prod.2 ⟨ha,
          (mem_relationImage _ _ _ _).2 ⟨hy, i, ix, entry⟩⟩
      · exact False.elim (empty (unused a ha))
    obtain ⟨delta, hd, small⟩ := initial beta hBeta
    have targetGround := M.relationImage_mem separation
      (M.insert_mem pairing unions (M.transitive hK hBeta) (M.transitive hK hBeta)) hA he
    obtain ⟨r, hr, code⟩ := small
    have contradiction : M.groundEmbeddable K delta :=
      ⟨relationCompose K (relationImage (insert beta beta) A e) delta f r,
        M.relationCompose_mem pairing unions powers separation hK targetGround
          (M.transitive hK hd) hf hr, bounded.compose code⟩
    exact cardinal.2 delta hd contradiction
  let g := ZFSet.sep (fun z => z ∈ ZFSet.prod K A) f
  have hg : g ∈ M.sets := M.injection_restriction_mem separation hK hA hf
  have partialCode : PartialFunctionCode K A g := by
    refine ⟨fun _ hz => (ZFSet.mem_sep.1 hz).2, ?_⟩
    intro x y z first second
    exact (functionCode_partial trace.1.to_isFunc).unique x y z
      (ZFSet.mem_sep.1 first).1 (ZFSet.mem_sep.1 second).1
  apply M.groundEmbeddable_of_partial_surjection pairing unions powers separation choice hK hA hg partialCode
  intro x hx
  obtain ⟨a, ha, entry⟩ := onto x hx
  exact ⟨a, ha, ZFSet.mem_sep.2 ⟨entry, ZFSet.pair_mem_prod.2 ⟨ha, hx⟩⟩⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing
open SetFormula
universe u

theorem GroundStrongLimit.cardinal_strongLimit {M : TransitiveGround.{u}} {K : ZFSet.{u}}
    (strong : GroundStrongLimit M K) : GroundCardinalStrongLimit M K :=
  fun κ hκ _ => strong κ hκ

namespace GroundCardinalStrongLimit
variable {M : TransitiveGround.{u}} {K : ZFSet.{u}}

theorem to_groundStrongLimit (strong : GroundCardinalStrongLimit M K)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hK : K ∈ M.sets) (ordinal : ordinalSetProperty K) : GroundStrongLimit M K := by
  intro α hα
  have hαM := M.transitive hK hα
  obtain ⟨κ, hκM, cardinal, bound, f, hf, injection, _, _⟩ :=
    M.exists_groundCardinalRepresentative pairing unions powers separation hαM
      (ordinalSetProperty_member ordinal hα)
  have hκ : κ ∈ K := bound.elim (fun equal => equal ▸ hα) (ordinal.1 α hα κ)
  exact (strong κ hκ cardinal).of_embeddable pairing unions powers separation
    (M.groundPower_mem powers hαM) (M.groundPower_mem powers hκM) hK
    (M.groundEmbeddable_power pairing unions powers separation hαM hκM ⟨f, hf, injection⟩)

theorem iff_groundStrongLimit
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hK : K ∈ M.sets) (ordinal : ordinalSetProperty K) :
    GroundCardinalStrongLimit M K ↔ GroundStrongLimit M K :=
  ⟨fun strong => strong.to_groundStrongLimit pairing unions powers separation hK ordinal,
    GroundStrongLimit.cardinal_strongLimit⟩

end GroundCardinalStrongLimit

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0)
variable (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
variable (infinite : Realize M.sets SetFormula.infinity Fin.elim0)

theorem groundOmegaOne_subset_of_not_countable {α : ZFSet.{u}}
    (ordinal : ordinalSetProperty α) (uncountable : ¬ M.groundEmbeddable α ZFSet.omega) :
    M.groundOmegaOne pairing unions powers separation collection infinite ⊆ α := by
  have spec := M.groundOmegaOne_spec pairing unions powers separation collection infinite
  obtain ⟨a, eqA⟩ := (ordinalSetProperty_iff α).1 ordinal
  obtain ⟨c, eqC⟩ := (ordinalSetProperty_iff _).1 spec.2.1
  by_cases lower : a < c
  · have inside : α ∈ M.groundOmegaOne pairing unions powers separation collection infinite := by
      rw [eqA, eqC, mem_ordinalCode_iff]
      exact lower
    exact False.elim (uncountable ((spec.2.2.1 α).1 inside).2.2)
  · rw [eqC, eqA, ordinalCode_subset_iff]
    exact le_of_not_gt lower

end TransitiveGround

namespace GroundInaccessibleConditions
variable {M : TransitiveGround.{u}} {K : ZFSet.{u}}
variable (conditions : GroundInaccessibleConditions M K)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0)
variable (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
variable (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
variable (hK : K ∈ M.sets)
include conditions hK

theorem groundOmegaOne_bound :
    ∃ α ∈ K, M.groundOmegaOne pairing unions powers separation collection infinite ⊆ α := by
  have hOmega := M.omega_mem separation infinite
  have hPower := M.groundPower_mem powers hOmega
  obtain ⟨α, hα, f, hf, injection⟩ := conditions.2.2.2 ZFSet.omega conditions.2.1
  have hAlpha := M.transitive hK hα
  have uncountable : ¬ M.groundEmbeddable α ZFSet.omega := by
    rintro ⟨g, hg, countable⟩
    apply M.groundPower_not_embeddable_self powers separation hOmega
    exact ⟨relationCompose (M.groundPower ZFSet.omega) α ZFSet.omega f g,
      M.relationCompose_mem pairing unions powers separation hPower hAlpha hOmega hf hg,
      injection.compose countable⟩
  exact ⟨α, hα, M.groundOmegaOne_subset_of_not_countable pairing unions powers separation
    collection infinite (ordinalSetProperty_member conditions.1 hα) uncountable⟩

theorem groundOmegaOne_below :
    GroundBelow M (M.groundOmegaOne pairing unions powers separation collection infinite) K := by
  obtain ⟨α, hα, subset⟩ := conditions.groundOmegaOne_bound pairing unions powers separation
    collection infinite hK
  let C := M.groundOmegaOne pairing unions powers separation collection infinite
  exact ⟨α, hα, identityFunctionGraph C,
    M.identityFunctionGraph_mem pairing unions powers separation
      (M.groundOmegaOne_spec pairing unions powers separation collection infinite).1,
    (identityFunctionGraph_injection C).retarget subset⟩

theorem groundOmegaOne_mem :
    M.groundOmegaOne pairing unions powers separation collection infinite ∈ K := by
  obtain ⟨α, hα, subset⟩ := conditions.groundOmegaOne_bound pairing unions powers separation
    collection infinite hK
  have spec := M.groundOmegaOne_spec pairing unions powers separation collection infinite
  obtain ⟨c, eqC⟩ := (ordinalSetProperty_iff _).1 spec.2.1
  obtain ⟨a, eqA⟩ := (ordinalSetProperty_iff α).1 (ordinalSetProperty_member conditions.1 hα)
  have bound : c ≤ a := by
    rw [eqC, eqA] at subset
    exact (ordinalCode_subset_iff c a).1 subset
  rcases lt_or_eq_of_le bound with lower | same
  · apply conditions.1.1 α hα
    rw [eqC, eqA, mem_ordinalCode_iff]
    exact lower
  · rw [eqC, same, ← eqA]
    exact hα

end GroundInaccessibleConditions




namespace GroundStandardInaccessible
variable {M : TransitiveGround.{u}} {K : ZFSet.{u}}
variable (standard : GroundStandardInaccessible M K)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (hK : K ∈ M.sets)
include standard pairing unions powers separation hK

theorem omega_mem : ZFSet.omega ∈ K := by
  obtain ⟨k, eqK⟩ := (ordinalSetProperty_iff K).1 standard.1.1
  by_cases greater : Ordinal.omega0 < k
  · rw [eqK, ← ordinalCode_omega, mem_ordinalCode_iff]
    exact greater
  · have subset : K ⊆ ZFSet.omega := by
      rw [eqK, ← ordinalCode_omega, ordinalCode_subset_iff]
      exact le_of_not_gt greater
    exact False.elim (standard.2.1 ⟨identityFunctionGraph K,
      M.identityFunctionGraph_mem pairing unions powers separation hK,
      (identityFunctionGraph_injection K).retarget subset⟩)

theorem to_conditions : GroundInaccessibleConditions M K :=
  ⟨standard.1.1, standard.omega_mem pairing unions powers separation hK,
    standard.2.2.1.regular standard.1.1,
    standard.2.2.2.to_groundStrongLimit pairing unions powers separation hK standard.1.1⟩

end GroundStandardInaccessible

namespace GroundInaccessibleConditions
variable {M : TransitiveGround.{u}} {K : ZFSet.{u}}

theorem to_standard (conditions : GroundInaccessibleConditions M K)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hK : K ∈ M.sets) : GroundStandardInaccessible M K :=
  ⟨conditions.internal_cardinal pairing unions powers separation hK,
    conditions.not_countable pairing unions powers separation hK,
    conditions.2.2.1.cofinal_regular, conditions.2.2.2.cardinal_strongLimit⟩

end GroundInaccessibleConditions

theorem groundStandardInaccessible_iff_conditions
    (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {K : ZFSet.{u}} (hK : K ∈ M.sets) :
    GroundStandardInaccessible M K ↔ GroundInaccessibleConditions M K :=
  ⟨fun standard => standard.to_conditions pairing unions powers separation hK,
    fun conditions => conditions.to_standard pairing unions powers separation hK⟩

end PartitionPilot.Forcing

end OAI
