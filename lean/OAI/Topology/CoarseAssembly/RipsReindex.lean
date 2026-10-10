import OAI.Topology.CoarseAssembly.RipsMapCalculus

namespace OAI

/-! # Isometric reindexing of coarse homology

The two sigma-type presentations of the fibered vertex set give isomorphic
Rips coarsening limits. This is used to compare the graph detector with the
vertex indexing of the spatial transfer.
-/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic

universe u

variable {X Y : Type u} [PseudoMetricSpace X] [PseudoMetricSpace Y]

theorem equiv_inverse_isometry (e : X ≃ Y) (he : Isometry e) : Isometry e.symm := by
  apply Isometry.of_dist_eq
  intro x y
  simpa only [Equiv.apply_symm_apply] using (he.dist_eq (e.symm x) (e.symm y)).symm

theorem mapPoint_equiv_inverse (e : X ≃ Y) (he : Isometry e) {r : ℝ}
    (p : Point X r) :
    mapPoint e.symm.toEmbedding (fun x y => ((equiv_inverse_isometry e he).dist_eq x y).le)
      (mapPoint e.toEmbedding (fun x y => (he.dist_eq x y).le) p) = p := by
  apply Point.ext
  apply Finsupp.ext
  intro x
  have h := mapPoint_weight_self e.symm.toEmbedding
    (fun x y => ((equiv_inverse_isometry e he).dist_eq x y).le)
    (mapPoint e.toEmbedding (fun x y => (he.dist_eq x y).le) p) (e x)
  calc
    _ = (mapPoint e.toEmbedding (fun x y => (he.dist_eq x y).le) p).weight (e x) := by
      simpa only [Equiv.toEmbedding_apply, Equiv.symm_apply_apply] using h
    _ = p.weight x := mapPoint_weight_self e.toEmbedding _ p x

def reindexHomology (e : X ≃ Y) (he : Isometry e) : KX1 X →+ KX1 Y :=
  (embeddingCoarsening e.toEmbedding (fun x y => (he.dist_eq x y).le)).homologyMap

theorem reindexHomology_inverse (e : X ≃ Y) (he : Isometry e) :
    (reindexHomology e.symm (equiv_inverse_isometry e he)).comp (reindexHomology e he) =
      AddMonoidHom.id (KX1 X) := by
  apply AddCommGroup.DirectLimit.hom_ext
  intro r
  apply AddMonoidHom.ext
  intro a
  change reindexHomology e.symm (equiv_inverse_isometry e he)
    (reindexHomology e he ((coarsening X).of r a)) = (coarsening X).of r a
  dsimp only [reindexHomology]
  rw [CoarseningMorphism.homologyMap_of, CoarseningMorphism.homologyMap_of]
  have hc : ((embeddingCoarsening e.symm.toEmbedding
        (fun x y => ((equiv_inverse_isometry e he).dist_eq x y).le)).atScale r).comp
      ((embeddingCoarsening e.toEmbedding (fun x y => (he.dist_eq x y).le)).atScale r) =
        CocompactMap.id (Point X (r : ℝ)) := by
    apply CocompactMap.ext
    intro p
    exact mapPoint_equiv_inverse e he p
  apply congrArg ((coarsening X).of r)
  rw [← AddMonoidHom.comp_apply, ← pushforward_comp, hc]
  exact DFunLike.congr_fun (pushforward_id (X := Point X (r : ℝ))) a

theorem reindexHomology_injective (e : X ≃ Y) (he : Isometry e) :
    Function.Injective (reindexHomology e he) := by
  intro a b hab
  have h := congrArg (reindexHomology e.symm (equiv_inverse_isometry e he)) hab
  have hi := reindexHomology_inverse e he
  simpa only [← AddMonoidHom.comp_apply, hi, AddMonoidHom.id_apply] using h

end CoarseAssembly.Rips

end

end OAI
