import Mathlib
import OAI.Topology.ArtinGroups.Realizations.RealizeSimplex
import OAI.Topology.ArtinGroups.Harmonic.PrismGrid
import OAI.Topology.ArtinGroups.Harmonic.PrismFlag

namespace OAI

namespace HarmonicArtin
open scoped unitInterval
open Simplicial CategoryTheory Opposite

attribute [local instance] Classical.decEq Classical.propDecidable

lemma prismMarginals_natural {n m:SimplexCategory} (u:n⟶m) (k:Fin (n.len+1))
    (w:Convexity.StdSimplex ℝ (Fin (n.len+2))) :
    prismMarginals (u.toOrderHom k) (Convexity.StdSimplex.map (prismOrdinal u k).toOrderHom w)=
      (Convexity.StdSimplex.map u.toOrderHom (prismMarginals k w).1,(prismMarginals k w).2) := by
  apply Prod.ext
  · change Convexity.StdSimplex.map (u.toOrderHom k).predAbove
      (Convexity.StdSimplex.map (prismOrdinal u k).toOrderHom w)=
      Convexity.StdSimplex.map u.toOrderHom (Convexity.StdSimplex.map k.predAbove w)
    rw [←Convexity.StdSimplex.map_comp,←Convexity.StdSimplex.map_comp]
    congr 1
    funext i
    exact congrArg Prod.fst (prismGrid_natural u k i)
  · apply Subtype.ext
    change (Convexity.StdSimplex.map (prismFlag (u.toOrderHom k))
      (Convexity.StdSimplex.map (prismOrdinal u k).toOrderHom w)).weights 0=
      (Convexity.StdSimplex.map (prismFlag k) w).weights 0
    rw [←Convexity.StdSimplex.map_comp]
    have he:prismFlag (u.toOrderHom k)∘(prismOrdinal u k).toOrderHom=prismFlag k:=by
      funext i
      exact congrArg Prod.snd (prismGrid_natural u k i)
    rw [he]

lemma prismCell_natural {n m:SimplexCategory} (u:n⟶m) (k:Fin (n.len+1))
    (p:Convexity.StdSimplex ℝ (Fin (n.len+1))×I) (hp:p∈PrismCell k) :
    (Convexity.StdSimplex.map u.toOrderHom p.1,p.2)∈PrismCell (u.toOrderHom k) := by
  have hm:=prismMarginals_natural u k (prismSimplex k p)
  rw [prismMarginals_simplex k p hp] at hm
  rw [←hm]
  exact prismMarginals_cell _ _

lemma map_prismSimplex {n m:SimplexCategory} (u:n⟶m) (k:Fin (n.len+1))
    (p:Convexity.StdSimplex ℝ (Fin (n.len+1))×I) (hp:p∈PrismCell k) :
    Convexity.StdSimplex.map (prismOrdinal u k).toOrderHom (prismSimplex k p)=
      prismSimplex (u.toOrderHom k) (Convexity.StdSimplex.map u.toOrderHom p.1,p.2) := by
  have hm:=prismMarginals_natural u k (prismSimplex k p)
  rw [prismMarginals_simplex k p hp] at hm
  rw [←hm]
  exact (prismSimplex_marginals _ _).symm

noncomputable def nervePrismPatch {P Q:Type*} [Preorder P] [Preorder Q]
    (f g:P→o Q) (h:∀p,f p≤g p) {n:SimplexCategory}
    (x:(nerve P).obj (op n)) (k:Fin (n.len+1)) :
    C(Convexity.StdSimplex ℝ (Fin (n.len+1))×I,|nerve Q|) :=
  (realizeSimplex (nerve Q) (nervePrism f g h x k)).comp (prismSimplex k)

lemma nervePrismPatch_natural {P Q:Type*} [Preorder P] [Preorder Q]
    (f g:P→o Q) (h:∀p,f p≤g p) {n m:SimplexCategory} (u:n⟶m)
    (x:(nerve P).obj (op m)) (k:Fin (n.len+1))
    (p:Convexity.StdSimplex ℝ (Fin (n.len+1))×I) (hp:p∈PrismCell k) :
    nervePrismPatch f g h ((nerve P).map u.op x) k p=
      nervePrismPatch f g h x (u.toOrderHom k) (Convexity.StdSimplex.map u.toOrderHom p.1,p.2) := by
  change realizeSimplex _ (nervePrism f g h ((nerve P).map u.op x) k) (prismSimplex k p)=_
  rw [nervePrism_natural,realizeSimplex_natural,map_prismSimplex _ _ _ hp]
  rfl

end HarmonicArtin

end OAI
