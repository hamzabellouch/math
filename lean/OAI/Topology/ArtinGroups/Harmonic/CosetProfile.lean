import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.PositiveSupportComponent
import OAI.Topology.ArtinGroups.Harmonic.CosetSum
import OAI.Topology.ArtinGroups.Geometry.SphericalCartanPos2

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

noncomputable def sourceCosetProfile (P:Deligne M) : ℕ→₀(S⊕Unit→ℝ) :=
  Finsupp.ofSupportFinite (fun k=>sourceCosetVector M P (k:ℤ))
    ((sourceCosetVector_support_finite M P).preimage
      (by intro a ha b hb he; exact Int.ofNat_inj.mp he))

@[simp] lemma sourceCosetProfile_apply (P:Deligne M) (k:ℕ) :
    sourceCosetProfile M P k=sourceCosetVector M P (k:ℤ) := rfl

def sourceActive (P:Deligne M) : Set S :=
  {i | i∉P.val.1 ∧ harmonicActive (framedCartan M) (.inr ()) (sourceCosetProfile M P) (.inl i)}

theorem sourceActive_spherical (P:Deligne M) : IsSpherical M (P.val.1 ∪ sourceActive M P) := by
  let K:Set S:=P.val.1 ∪ sourceActive M P
  let T:Set (S⊕Unit):=(Sum.inl:S→S⊕Unit) '' P.val.1
  let L:Set (S⊕Unit):=(Sum.inl:S→S⊕Unit) '' K
  have hL:((framedCartan M).submatrix ((↑):L→S⊕Unit) Subtype.val).PosDef := by
    apply harmonic_active_posDef (framedCartan M) (framedCartan_symm M)
      (framedCartan_off M) (fun i=>by rw [framedCartan_diag]; norm_num) (.inr ())
      (fun i hi=>by cases i with
        | inl i => norm_num [framedCartan]
        | inr u => cases u; exact (hi rfl).elim)
      (sourceCosetProfile M P) (fun k i=>sourceCosetVector_nonneg M P k i)
      (by rw [sourceCosetProfile_apply,sourceCosetVector_frame]; norm_num)
      T (framed_spherical_posDef M P.val.1 P.property.1)
    · intro k i hi
      exact sourceHarmonicAt_harmonic M P.val.1 P.property.1 _ k ⟨i,hi⟩
    · rintro ⟨i,hi,he⟩; exact Sum.inl_ne_inr he
    · rintro i ⟨j,(hj|hj),rfl⟩
      · exact Or.inl ⟨j,hj,rfl⟩
      · exact Or.inr hj.2
  let f:K→L:=fun i=>⟨.inl (i:S),⟨i,i.property,rfl⟩⟩
  have hf:Function.Injective f:=by
    intro i j h
    exact Subtype.ext (Sum.inl.inj (congrArg Subtype.val h))
  apply Geometric.spherical_of_cartan_posDef M K
  convert hL.submatrix hf using 1
  ext i j
  rfl

end HarmonicArtin

end OAI
