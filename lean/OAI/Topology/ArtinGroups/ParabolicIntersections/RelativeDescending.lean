import OAI.Topology.ArtinGroups.ParabolicIntersections.RelativeLowerConnected
import OAI.Topology.ArtinGroups.ParabolicIntersections.RelativeUpperConnected

namespace OAI

/-! Combining upper and lower descending neighborhoods. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)
  (U:Set (S ⊕ Unit)) (cutoff:ℤ)

lemma relativePathWithin_mono {V:Type} {adj:V→V→Prop} {p q:V→Prop}
    (hpq:∀v,p v→q v) {a b:V} (h:PathWithin adj p a b) : PathWithin adj q a b := by
  induction h with
  | refl => exact .refl
  | tail _ he ih => exact ih.tail ⟨hpq _ he.1,hpq _ he.2.1,he.2.2⟩

lemma relativePathWithin_single {V:Type} {adj:V→V→Prop} {p:V→Prop}
    {a b:V} (ha:p a) (hb:p b) (h:adj a b) : PathWithin adj p a b :=
  Relation.ReflTransGen.single ⟨ha,hb,h⟩

omit [Fintype S] [LinearOrder S] in
lemma relative_vertex_avoids_frame {Y:Set S} {x:Artin M}
    (hf:f∉Y) (hx:x∈artinParabolic M {f}ᶜ) (P:RelativeVertex M Y x) :
    sourceCosetRepresentative M P.val∈artinParabolic M {f}ᶜ := by
  have hg:=P.property.2 (sourceCosetRepresentative_mem M P.val)
  have hY:Y⊆({f}ᶜ:Set S):=fun i hi he=>hf (he ▸ hi)
  have hm:=(artinParabolic M {f}ᶜ).mul_mem (artinParabolic_mono M hY hg) hx
  simpa only [_root_.mul_assoc,inv_mul_cancel,_root_.mul_one] using hm

theorem relative_descending_connected {Y:Set S} {x:Artin M} (P:RelativeVertex M Y x)
    (hYU:∀i∈Y,(.inl i:S⊕Unit)∈U)
    (hU:U⊆Set.range (Sum.inl:S→S⊕Unit)) (hf:(.inl f:S⊕Unit)∉U)
    (hxA:sourceCosetRepresentative M P.val∈artinParabolic M {f}ᶜ)
    (A B:RelativeVertex M Y x)
    (hA:relativeAdjacent M P A) (ha:relativeHeight M f U cutoff A.val<relativeHeight M f U cutoff P.val)
    (hB:relativeAdjacent M P B) (hb:relativeHeight M f U cutoff B.val<relativeHeight M f U cutoff P.val) :
    PathWithin (relativeAdjacent M) (fun V=>relativeHeight M f U cutoff V.val<relativeHeight M f U cutoff P.val) A B := by
  have hneA:P≠A:=by intro he;subst A;exact lt_irrefl _ ha
  have hneB:P≠B:=by intro he;subst B;exact lt_irrefl _ hb
  rcases hA with hA|hA <;> rcases hB with hB|hB
  · exact relativePathWithin_mono (fun _ h=>h.2)
      (relative_descending_upper_connected M f U cutoff Y x P hYU A B
        ⟨lt_of_le_of_ne hA hneA,ha⟩ ⟨lt_of_le_of_ne hB hneB,hb⟩)
  · exact relativePathWithin_single ha hb (Or.inr (hB.trans hA))
  · exact relativePathWithin_single ha hb (Or.inl (hA.trans hB))
  · exact relativePathWithin_mono (fun _ h=>h.2)
      (relative_descending_lower_connected M f U cutoff P hU hf hxA A B
        ⟨lt_of_le_of_ne hA (Ne.symm hneA),ha⟩ ⟨lt_of_le_of_ne hB (Ne.symm hneB),hb⟩)

end HarmonicArtin.ParabolicIntersections

end OAI
