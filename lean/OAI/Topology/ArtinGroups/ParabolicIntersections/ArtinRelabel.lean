import OAI.Topology.ArtinGroups.Harmonic.RestrictedArtinHom
import OAI.Topology.ArtinGroups.Coxeter.AltListMap
import OAI.Topology.ArtinGroups.Coxeter.AlternatingLiftProd

namespace OAI

/-! Maps of Artin presentations induced by label-preserving maps. -/
namespace HarmonicArtin.ParabolicIntersections
open CoxeterExchange
variable {S T : Type} (M : CoxeterMatrix S) (N : CoxeterMatrix T)
    (f : S → T) (hf : ∀ i j, N (f i) (f j)=M i j)

include hf in
private lemma artinMap_relators : ∀ r ∈ braidRelators M,
    FreeGroup.lift (fun s => generator N (f s)) r=1 := by
  rintro r ⟨⟨i,j⟩,rfl⟩
  rw [map_mul,map_inv,alternating_lift_prod,alternating_lift_prod]
  apply mul_inv_eq_one.mpr
  have h := wordArtin_braid N (f i) (f j)
  rw [hf] at h
  simpa only [wordArtin,←altList_map,List.map_map,Function.comp_def] using h

noncomputable def artinMap : Artin M →* Artin N :=
  PresentedGroup.toGroup (artinMap_relators M N f hf)

@[simp] lemma artinMap_generator (s : S) :
    artinMap M N f hf (generator M s)=generator N (f s) := PresentedGroup.toGroup.of _

lemma artinMap_leftInverse (g : T → S) (hg : ∀ i j, M (g i) (g j)=N i j)
    (hgf : Function.LeftInverse g f) :
    Function.LeftInverse (artinMap N M g hg) (artinMap M N f hf) := by
  have he : (artinMap N M g hg).comp (artinMap M N f hf)=MonoidHom.id (Artin M) := by
    apply PresentedGroup.ext
    intro s
    change artinMap N M g hg (artinMap M N f hf (generator M s))=generator M s
    rw [artinMap_generator,artinMap_generator,hgf s]
  intro a
  exact DFunLike.congr_fun he a

end HarmonicArtin.ParabolicIntersections

end OAI
