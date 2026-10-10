import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.PrismSimplexZero

namespace OAI

namespace HarmonicArtin
universe u
open scoped unitInterval
open Simplicial CategoryTheory Opposite

attribute [local instance] Classical.decEq Classical.propDecidable

noncomputable def nerveOrderMap {P Q:Type u} [Preorder P] [Preorder Q] (f:P→oQ) :
    C(|nerve P|,|nerve Q|) := (SSet.toTop.map (nerveMap f.toFunctor)).hom

noncomputable def nervePrismMap {P Q:Type u} [Preorder P] [Preorder Q]
    (f g:P→oQ) (h:∀p,f p≤g p) : nerve P⟶TopCat.toSSet.obj (TopCat.of C(I,|nerve Q|)) where
  app n:=↾fun x=>(TopCat.toSSetObjEquiv _ n).symm (nervePrismSimplex f g h x)
  naturality {n m} a:=by
    apply ConcreteCategory.hom_ext
    intro x
    apply (TopCat.toSSetObjEquiv _ m).injective
    ext z t
    exact nervePrismSimplex_natural f g h a.unop x z t

noncomputable def nervePrismReal {P Q:Type u} [Preorder P] [Preorder Q]
    (f g:P→oQ) (h:∀p,f p≤g p) : C(|nerve P|,C(I,|nerve Q|)) :=
  ((sSetTopAdj.homEquiv _ _).symm (nervePrismMap f g h)).hom

noncomputable def nervePathEvaluate (Q:Type u) [Preorder Q] (t:I) :
    TopCat.of C(I,|nerve Q|)⟶|nerve Q| :=
  TopCat.ofHom ⟨fun f=>f t,continuous_eval_const t⟩

lemma nervePrismReal_zero {P Q:Type u} [Preorder P] [Preorder Q]
    (f g:P→oQ) (h:∀p,f p≤g p) :
    TopCat.ofHom (nervePrismReal f g h)≫nervePathEvaluate Q 0=
      SSet.toTop.map (nerveMap g.toFunctor) := by
  apply (sSetTopAdj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right]
  simp only [nervePrismReal,TopCat.ofHom_hom,Equiv.apply_symm_apply]
  rw [Adjunction.homEquiv_unit]
  ext n x
  apply (TopCat.toSSetObjEquiv _ n).injective
  ext z
  change nervePrismSimplex f g h x z 0=
    SSet.toTop.map (nerveMap g.toFunctor) (realizeSimplex (nerve P) x z)
  rw [nervePrismSimplex_zero,realizeSimplex_map]

lemma nervePrismReal_one {P Q:Type u} [Preorder P] [Preorder Q]
    (f g:P→oQ) (h:∀p,f p≤g p) :
    TopCat.ofHom (nervePrismReal f g h)≫nervePathEvaluate Q 1=
      SSet.toTop.map (nerveMap f.toFunctor) := by
  apply (sSetTopAdj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right]
  simp only [nervePrismReal,TopCat.ofHom_hom,Equiv.apply_symm_apply]
  rw [Adjunction.homEquiv_unit]
  ext n x
  apply (TopCat.toSSetObjEquiv _ n).injective
  ext z
  change nervePrismSimplex f g h x z 1=
    SSet.toTop.map (nerveMap f.toFunctor) (realizeSimplex (nerve P) x z)
  rw [nervePrismSimplex_one,realizeSimplex_map]

noncomputable def nerveOrderComparisonHomotopy {P Q:Type u} [Preorder P] [Preorder Q]
    (f g:P→oQ) (h:∀p,f p≤g p) :
    ContinuousMap.Homotopy (nerveOrderMap f) (nerveOrderMap g) :=
  (show ContinuousMap.Homotopy (nerveOrderMap g) (nerveOrderMap f) from {
    toFun:=fun p=>nervePrismReal f g h p.2 p.1
    continuous_toFun:=(nervePrismReal f g h).uncurry.continuous.comp continuous_swap
    map_zero_left:=fun p=>ConcreteCategory.congr_hom (nervePrismReal_zero f g h) p
    map_one_left:=fun p=>ConcreteCategory.congr_hom (nervePrismReal_one f g h) p }).symm

lemma nerveOrderMap_id (P:Type u) [Preorder P] :
    nerveOrderMap (OrderHom.id (α:=P))=ContinuousMap.id |nerve P| := by
  have he:nerveMap (OrderHom.id (α:=P)).toFunctor=𝟙 (nerve P):=by
    ext n x
    rfl
  change (SSet.toTop.map _).hom=_
  rw [he,CategoryTheory.Functor.map_id]
  rfl

noncomputable def nerveVertex (Q:Type u) [Preorder Q] (c:Q) : |nerve Q| :=
  realizeSimplex (nerve Q) (ComposableArrows.mk₀ c) (Convexity.StdSimplex.single 0)

lemma simplex_zero_unique (z:Convexity.StdSimplex ℝ (Fin 1)) :
    z=Convexity.StdSimplex.single 0 :=
  Subsingleton.elim _ _

lemma realizeSimplex_const {P Q:Type u} [Preorder P] [Preorder Q] (c:Q)
    {n:SimplexCategory} (x:(nerve P).obj (op n))
    (z:Convexity.StdSimplex ℝ (Fin (n.len+1))) :
    realizeSimplex (nerve Q) ((nerveMap (OrderHom.const P c).toFunctor).app (op n) x) z=nerveVertex Q c := by
  let a:n⟶⦋0⦌:=SimplexCategory.mkHom (OrderHom.const _ 0)
  have he:(nerve Q).map a.op (ComposableArrows.mk₀ c)=
      (nerveMap (OrderHom.const P c).toFunctor).app (op n) x:=by
    apply nerve.ext_of_isThin
    rfl
  have hh:=realizeSimplex_natural (nerve Q) a (ComposableArrows.mk₀ c) z
  rw [he] at hh
  exact hh.trans (congrArg (realizeSimplex (nerve Q) (ComposableArrows.mk₀ c))
    (simplex_zero_unique (Convexity.StdSimplex.map a.toOrderHom z)))

lemma nerveOrderMap_const {P Q:Type u} [Preorder P] [Preorder Q] (c:Q) :
    nerveOrderMap (OrderHom.const P c)=ContinuousMap.const _ (nerveVertex Q c) := by
  have he:SSet.toTop.map (nerveMap (OrderHom.const P c).toFunctor)=TopCat.const (X:=|nerve P|) (nerveVertex Q c):=by
    apply (sSetTopAdj.homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit,Adjunction.homEquiv_unit]
    ext n x
    apply (TopCat.toSSetObjEquiv _ n).injective
    ext z
    change SSet.toTop.map (nerveMap (OrderHom.const P c).toFunctor) (realizeSimplex (nerve P) x z)=nerveVertex Q c
    rw [realizeSimplex_map,realizeSimplex_const]
  exact congrArg TopCat.Hom.hom he

theorem nerve_contractible_of_order_clip {P:Type u} [Preorder P]
    (e:P→o P) (c:P) (he:∀p,e p≤p) (hc:∀p,e p≤c) : ContractibleSpace |nerve P| := by
  apply (contractible_iff_id_nullhomotopic _).mpr
  refine ⟨nerveVertex P c,?_⟩
  have hh:ContinuousMap.Homotopic (nerveOrderMap (OrderHom.id (α:=P)))
      (nerveOrderMap (OrderHom.const P c)):=
    ⟨(nerveOrderComparisonHomotopy e (OrderHom.id (α:=P)) he).symm.trans
      (nerveOrderComparisonHomotopy e (OrderHom.const P c) hc)⟩
  simpa only [nerveOrderMap_id,nerveOrderMap_const] using hh

end HarmonicArtin

end OAI
