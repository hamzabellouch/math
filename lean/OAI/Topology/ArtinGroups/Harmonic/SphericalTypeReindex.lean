import Mathlib
import OAI.Topology.ArtinGroups.Realizations.CellDeligne
import OAI.Topology.ArtinGroups.Harmonic.ArtinReindex

namespace OAI

namespace HarmonicArtin
open CoxeterExchange

attribute [local instance] Classical.decEq Classical.propDecidable
universe u v
variable {S : Type u} {T : Type v} (M : CoxeterMatrix S) (e : S ≃ T)

lemma wordArtin_reindex (w : List S) :
    wordArtin (M.reindex e) (w.map e) = artinReindex M e (wordArtin M w) := by
  induction w with
  | nil => simp [wordArtin]
  | cons s w ih =>
    simpa only [wordArtin,List.map_cons,List.prod_cons,map_mul,artinReindex_generator]
      using congrArg (generator (M.reindex e) (e s) * ·) ih

lemma wordCoxeter_reindex (w : List S) :
    wordCoxeter (M.reindex e) (w.map e) = (M.reindexGroupEquiv e).symm (wordCoxeter M w) := by
  exact (wordProd_equiv M.toCoxeterSystem (M.reindex e).toCoxeterSystem e
    (M.reindexGroupEquiv e).symm (fun _ => rfl) w).symm

lemma coxeter_length_reindex (x : M.Group) :
    (M.reindex e).toCoxeterSystem.length ((M.reindexGroupEquiv e).symm x) =
      M.toCoxeterSystem.length x :=
  length_equiv M.toCoxeterSystem (M.reindex e).toCoxeterSystem e
    (M.reindexGroupEquiv e).symm (fun _ => rfl) x

lemma minimal_reindex (A : Set S) (x : M.Group) :
    (∀ w : coxeterParabolic (M.reindex e) (e '' A),
      (M.reindex e).toCoxeterSystem.length ((M.reindexGroupEquiv e).symm x) ≤
        (M.reindex e).toCoxeterSystem.length ((M.reindexGroupEquiv e).symm x * w.val)) ↔
    (∀ w : coxeterParabolic M A,
      M.toCoxeterSystem.length x ≤ M.toCoxeterSystem.length (x * w.val)) := by
  let f := (M.reindexGroupEquiv e).symm
  let p : coxeterParabolic M A ≃* coxeterParabolic (M.reindex e) (e '' A) :=
    (f.subgroupMap (coxeterParabolic M A)).trans (MulEquiv.subgroupCongr (coxeterParabolic_reindex M e A))
  constructor
  · intro h w
    have hh := h (p w)
    change (M.reindex e).toCoxeterSystem.length (f x) ≤
      (M.reindex e).toCoxeterSystem.length (f x * f w.val) at hh
    simpa only [←map_mul,f,coxeter_length_reindex] using hh
  · intro h w
    obtain ⟨a,rfl⟩ := p.surjective w
    change (M.reindex e).toCoxeterSystem.length (f x) ≤
      (M.reindex e).toCoxeterSystem.length (f x * f a.val)
    simpa only [←map_mul,f,coxeter_length_reindex] using h a

noncomputable def sphericalTypeReindex : SphericalType M ≃ SphericalType (M.reindex e) where
  toFun A := ⟨e '' A.val,(spherical_reindex M e A.val).mpr A.property⟩
  invFun B := ⟨e ⁻¹' B.val,(spherical_reindex M e (e ⁻¹' B.val)).mp (by
    simpa only [Set.image_preimage_eq _ e.surjective] using B.property)⟩
  left_inv A := by apply Subtype.ext; exact Set.preimage_image_eq _ e.injective
  right_inv B := by apply Subtype.ext; exact Set.image_preimage_eq _ e.surjective

noncomputable def liftedReindexEquiv : LiftedCell M ≃ LiftedCell (M.reindex e) :=
  (artinReindex M e).toEquiv.prodCongr (sphericalTypeReindex M e)

lemma reindex_letters (A : Set S) (w : List S) :
    (∀ t ∈ w.map e, t ∈ e '' A) ↔ ∀ s ∈ w, s ∈ A := by
  constructor
  · intro h s hs
    obtain ⟨r,hr,he⟩ := h (e s) (List.mem_map.mpr ⟨s,hs,rfl⟩)
    exact e.injective he ▸ hr
  · intro h t ht
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ht
    exact ⟨s,h s hs,rfl⟩

lemma liftedFace_reindex_iff (a b : LiftedCell M) :
    LiftedFace (M.reindex e) (liftedReindexEquiv M e a) (liftedReindexEquiv M e b) ↔
      LiftedFace M a b := by
  change ((e '' a.2.val ⊆ e '' b.2.val) ∧ ∃ w : List T,
    (∀ s ∈ w, s ∈ e '' b.2.val) ∧
    (M.reindex e).toCoxeterSystem.length (wordCoxeter (M.reindex e) w) = w.length ∧
    (∀ v : coxeterParabolic (M.reindex e) (e '' a.2.val),
      (M.reindex e).toCoxeterSystem.length (wordCoxeter (M.reindex e) w) ≤
      (M.reindex e).toCoxeterSystem.length (wordCoxeter (M.reindex e) w * v.val)) ∧
    artinReindex M e a.1 = artinReindex M e b.1 * wordArtin (M.reindex e) w) ↔ _
  rw [Set.image_subset_image_iff e.injective]
  constructor
  · rintro ⟨ht,w,hw,hr,hm,he⟩
    let q := w.map e.symm
    have hq : q.map e = w := by simp [q,List.map_map]
    rw [←hq,reindex_letters] at hw
    rw [←hq,wordCoxeter_reindex,coxeter_length_reindex,List.length_map] at hr
    rw [←hq,wordCoxeter_reindex,minimal_reindex] at hm
    rw [←hq,wordArtin_reindex,←map_mul] at he
    exact ⟨ht,q,hw,hr,hm,(artinReindex M e).injective he⟩
  · rintro ⟨ht,w,hw,hr,hm,he⟩
    refine ⟨ht,w.map e,(reindex_letters e b.2.val w).mpr hw,?_,?_,?_⟩
    · simpa only [wordCoxeter_reindex,coxeter_length_reindex,List.length_map] using hr
    · rw [wordCoxeter_reindex,minimal_reindex]
      exact hm
    · simpa only [wordArtin_reindex,←map_mul] using congrArg (artinReindex M e) he

noncomputable def liftedReindex : LiftedCell M ≃o LiftedCell (M.reindex e) where
  toEquiv := liftedReindexEquiv M e
  map_rel_iff' := by
    intro a b
    rw [lifted_le_iff_face,lifted_le_iff_face]
    exact liftedFace_reindex_iff M e a b

end HarmonicArtin

end OAI
