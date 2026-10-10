import Mathlib
import OAI.RingTheory.Multiplicity.CechExact

namespace OAI

noncomputable section
namespace Lech.FiniteModuleCech
open CategoryTheory CategoryTheory.Limits
universe u
variable {R : Type u} [CommRing R] {ι : Type}
variable (D E : Diagram R ι)

def prodDiagram : Diagram R ι where
  obj s := ModuleCat.of R (D.obj s × E.obj s)
  res {s t} hst := ModuleCat.ofHom ((D.res hst).hom.prodMap (E.res hst).hom)
  res_self s := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change ((D.res _).hom x.1,(E.res _).hom x.2)=x
    rw [D.res_self,E.res_self]
    rfl
  res_comp {s t v} hst htv := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change ((D.res htv).hom ((D.res hst).hom x.1),(E.res htv).hom ((E.res hst).hom x.2))=_
    exact Prod.ext (congrArg (fun f : D.obj s ⟶ D.obj v => f.hom x.1) (D.res_comp hst htv))
      (congrArg (fun f : E.obj s ⟶ E.obj v => f.hom x.2) (E.res_comp hst htv))

variable {D E} {G : Diagram R ι}
def Map.prodLift (φ : Map G D) (ψ : Map G E) : Map G (prodDiagram D E) where
  app s := ModuleCat.ofHom ((φ.app s).hom.prod (ψ.app s).hom)
  naturality {s t} hst := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact Prod.ext (congrArg (fun f : G.obj s ⟶ D.obj t => f.hom x) (φ.naturality hst))
      (congrArg (fun f : G.obj s ⟶ E.obj t => f.hom x) (ψ.naturality hst))

def Map.prodDesc (φ : Map D G) (ψ : Map E G) : Map (prodDiagram D E) G where
  app s := ModuleCat.ofHom ((φ.app s).hom.coprod (ψ.app s).hom)
  naturality {s t} hst := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (φ.app t).hom ((D.res hst).hom x.1)+(ψ.app t).hom ((E.res hst).hom x.2)=
      (G.res hst).hom ((φ.app s).hom x.1+(ψ.app s).hom x.2)
    rw [map_add]
    exact congrArg₂ (·+·) (congrArg (fun f : D.obj s ⟶ G.obj t => f.hom x.1) (φ.naturality hst))
      (congrArg (fun f : E.obj s ⟶ G.obj t => f.hom x.2) (ψ.naturality hst))

def Map.neg (φ : Map D E) : Map D E where
  app s := -(φ.app s)
  naturality {s t} hst := by rw [Preadditive.comp_neg,Preadditive.neg_comp,φ.naturality hst]

variable (D E)
def prodInl : Map D (prodDiagram D E) where
  app s := ModuleCat.ofHom (LinearMap.inl R (D.obj s) (E.obj s))
  naturality {s t} hst := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change ((D.res hst).hom x,0)=((D.res hst).hom x,(E.res hst).hom 0)
    rw [map_zero]
def prodSnd : Map (prodDiagram D E) E where
  app s := ModuleCat.ofHom (LinearMap.snd R (D.obj s) (E.obj s))
  naturality := by intros; rfl
lemma prod_comp_zero (s : Finset ι) : (prodInl D E).app s ≫ (prodSnd D E).app s=0 := rfl
lemma prod_shortExact (s : Finset ι) :
    (diagramShortComplex (prodInl D E) (prodSnd D E) (prod_comp_zero D E) s).ShortExact where
  mono_f := (ModuleCat.mono_iff_injective _).mpr (by
    intro x y h
    exact congrArg Prod.fst h)
  epi_g := (ModuleCat.epi_iff_surjective _).mpr (fun y => ⟨(0,y),rfl⟩)
  exact := (ShortComplex.moduleCat_exact_iff _).mpr (by
    intro y hy
    exact ⟨y.1,Prod.ext rfl hy.symm⟩)
end Lech.FiniteModuleCech

end

end OAI
