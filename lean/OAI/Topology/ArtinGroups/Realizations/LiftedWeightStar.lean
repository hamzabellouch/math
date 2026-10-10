import Mathlib
import OAI.Topology.ArtinGroups.Realizations.CellUnion

namespace OAI

namespace HarmonicArtin
open Topology Set Filter CoxeterExchange

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type*} [Fintype S] [DecidableEq S] (M : CoxeterMatrix S)

omit [DecidableEq S] in
lemma liftedDeck_incident_finite (a b : LiftedCell M) :
    {g : Artin M | liftedDeck M g a ≤ b ∨ b ≤ liftedDeck M g a}.Finite := by
  apply (((lifted_closed_cell_finite M b).image (fun c => c.1*a.1⁻¹)).union
    ((lifted_closed_cell_finite M a).image (fun c => b.1*c.1⁻¹))).subset
  intro g hg
  rcases hg with hab|hba
  · exact Or.inl ⟨liftedDeck M g a,hab,by change g*a.1*a.1⁻¹=g; simp [mul_assoc]⟩
  · refine Or.inr ⟨liftedDeck M g⁻¹ b,?_,?_⟩
    · have h := (liftedDeck M g).symm.monotone hba
      rw [OrderIso.symm_apply_apply] at h
      exact h
    · change b.1*(g⁻¹*b.1)⁻¹=g
      simp [mul_inv_rev]

noncomputable def liftedWeightStar (a : LiftedCell M) : Set (OrderWeights (LiftedCell M)) :=
  {x | 0 < x.weights a}

omit [Fintype S] [DecidableEq S] in
lemma liftedWeightStar_open (a : LiftedCell M) : IsOpen (liftedWeightStar M a) :=
  isOpen_lt continuous_const (weightEval_continuous a)

omit [DecidableEq S] in
lemma liftedWeightStar_finite_translates (a b : LiftedCell M) :
    {g : Artin M | ((g • ·) '' liftedWeightStar M a ∩ liftedWeightStar M b).Nonempty}.Finite := by
  apply (liftedDeck_incident_finite M a b).subset
  rintro g ⟨y,⟨x,hx,rfl⟩,hy⟩
  have ha : liftedDeck M g a ∈ (g • x).weights.support := by
    rw [Finsupp.mem_support_iff,liftedWeights_smul_apply]
    exact ne_of_gt hx
  have hb : b ∈ (g • x).weights.support := Finsupp.mem_support_iff.mpr (ne_of_gt hy)
  exact (g • x).chain _ ha _ hb

instance sourceDeckT2 : T2Space (SalvettiDeckQuotient M) := by
  change T2Space (Quotient (MulAction.orbitRel (Artin M) (OrderWeights (LiftedCell M))))
  rw [t2Space_iff_nhds]
  let := MulAction.orbitRel (Artin M) (OrderWeights (LiftedCell M))
  let f : OrderWeights (LiftedCell M) → Quotient
      (MulAction.orbitRel (Artin M) (OrderWeights (LiftedCell M))) := Quotient.mk'
  have fop : IsOpenMap f := isOpenMap_quotient_mk'_mul
  rintro ⟨x⟩ ⟨y⟩ (hxy : f x ≠ f y)
  have hgxy : ∀ g : Artin M,g • x ≠ y := by
    intro element equality
    exact hxy.symm (Quotient.sound ⟨element,equality⟩)
  obtain ⟨a,ha⟩ := x.support_nonempty
  obtain ⟨b,hb⟩ := y.support_nonempty
  let U := liftedWeightStar M a
  let V := liftedWeightStar M b
  have hU : U ∈ 𝓝 x := (liftedWeightStar_open M a).mem_nhds
    (lt_of_le_of_ne (x.nonneg a) (Ne.symm (Finsupp.mem_support_iff.mp ha)))
  have hV : V ∈ 𝓝 y := (liftedWeightStar_open M b).mem_nhds
    (lt_of_le_of_ne (y.nonneg b) (Ne.symm (Finsupp.mem_support_iff.mp hb)))
  let K := {g : Artin M | ((g • ·) '' U ∩ V).Nonempty}
  have hK : K.Finite := liftedWeightStar_finite_translates M a b
  choose u v hu hv huv using fun g => t2_separation_nhds (hgxy g)
  let U' := (⋂ g ∈ K,(g • ·) ⁻¹' u g) ∩ U
  let V' := (⋂ g ∈ K,v g) ∩ V
  have hU' : f '' U' ∈ 𝓝 (f x) := by
    apply fop.image_mem_nhds
    refine inter_mem ((biInter_mem hK).mpr (fun g _ => ?_)) hU
    exact (continuous_const_smul g).continuousAt (hu g)
  have hV' : f '' V' ∈ 𝓝 (f y) :=
    fop.image_mem_nhds (inter_mem ((biInter_mem hK).mpr (fun g _ => hv g)) hV)
  refine ⟨f '' U',hU',f '' V',hV',MulAction.disjoint_image_image_iff.mpr ?_⟩
  rintro z ⟨hz,hzU⟩ g ⟨hgz,hgzV⟩
  have hg : g ∈ K := ⟨g • z,mem_image_of_mem _ hzU,hgzV⟩
  exact (huv g).le_bot ⟨mem_iInter₂.mp hz g hg,mem_iInter₂.mp hgz g hg⟩

instance sourceSalvettiT2 : T2Space (SourceSalvetti M) :=
  (sourceSalvettiHomeomorph M).isEmbedding.t2Space

instance sourceModelCompact (T : SphericalType M) : CompactSpace (SourceModelCell M T) :=
  isCompact_iff_compactSpace.mp (Geometric.permutahedron_compact (restrictedMatrix M T.val))

instance sourceSalvettiCompact : CompactSpace (SourceSalvetti M) :=
  Quotient.compactSpace

end HarmonicArtin

end OAI
