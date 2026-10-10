import Mathlib
import OAI.Topology.ArtinGroups.Geometry.RestrictionLength

namespace OAI

namespace HarmonicArtin.CoxeterExchange
variable {B C W H : Type*} [Group W] [Group H]
  {M : CoxeterMatrix B} {N : CoxeterMatrix C}

lemma wordProd_equiv (cs : CoxeterSystem M W) (ds : CoxeterSystem N H)
    (e : B ≃ C) (f : W ≃* H) (hf : ∀ i, f (cs.simple i)=ds.simple (e i)) (u : List B) :
    f (cs.wordProd u)=ds.wordProd (u.map e) := by
  induction u with
  | nil => simp
  | cons i u ih => simp only [CoxeterSystem.wordProd_cons,map_mul,hf,ih,List.map_cons]

lemma length_equiv (cs : CoxeterSystem M W) (ds : CoxeterSystem N H)
    (e : B ≃ C) (f : W ≃* H) (hf : ∀ i, f (cs.simple i)=ds.simple (e i)) (w : W) :
    ds.length (f w)=cs.length w := by
  apply Nat.le_antisymm
  · obtain ⟨u,hu,rfl⟩ := cs.exists_isReduced w
    rw [wordProd_equiv cs ds e f hf,hu.eq]
    simpa using ds.length_wordProd_le (u.map e)
  · have hg : ∀ j, f.symm (ds.simple j)=cs.simple (e.symm j) := by
      intro j
      apply f.injective
      simp only [f.apply_symm_apply,hf,e.apply_symm_apply]
    obtain ⟨v,hv,he⟩ := ds.exists_isReduced (f w)
    have hw : w=f.symm (ds.wordProd v) := by rw [← he]; simp
    conv_lhs => rw [hw,wordProd_equiv ds cs e.symm f.symm hg]
    rw [he,hv.eq]
    simpa using cs.length_wordProd_le (v.map e.symm)

lemma reduced_equiv (cs : CoxeterSystem M W) (ds : CoxeterSystem N H)
    (e : B ≃ C) (f : W ≃* H) (hf : ∀ i, f (cs.simple i)=ds.simple (e i)) (u : List B) :
    ds.IsReduced (u.map e) ↔ cs.IsReduced u := by
  simp only [CoxeterSystem.IsReduced,← wordProd_equiv cs ds e f hf,length_equiv cs ds e f hf,
    List.length_map]

lemma system_reduced_iff (cs : CoxeterSystem M W) (u : List B) :
    M.toCoxeterSystem.IsReduced u ↔ cs.IsReduced u := by
  simpa using reduced_equiv cs M.toCoxeterSystem (Equiv.refl B) cs.mulEquiv
    (fun i => cs.mulEquiv.apply_symm_apply _) u

lemma reindex_reduced (cs : CoxeterSystem M W) (e : B ≃ C) (u : List B) :
    (cs.reindex e).IsReduced (u.map e) ↔ cs.IsReduced u := by
  exact reduced_equiv cs (cs.reindex e) e (MulEquiv.refl W)
    (fun i => by simp) u

theorem embedding_reduced [Fintype C] [DecidableEq C]
    (f : B → C) (hi : Function.Injective f) (hm : ∀ i j, N (f i) (f j)=M i j)
    (u : List B) (hu : M.toCoxeterSystem.IsReduced u) :
    N.toCoxeterSystem.IsReduced (u.map f) := by
  classical
  let e : B ≃ Set.range f := Equiv.ofInjective f hi
  have hM : M.reindex e=restrictedMatrix N (Set.range f) := by
    ext i j
    simp only [CoxeterMatrix.reindex_apply,restrictedMatrix_apply]
    have hi' : f (e.symm i)=i.val := congrArg Subtype.val (e.apply_symm_apply i)
    have hj' : f (e.symm j)=j.val := congrArg Subtype.val (e.apply_symm_apply j)
    rw [← hi',← hj',hm]
  have he : (M.toCoxeterSystem.reindex e).IsReduced (u.map e) :=
    (reindex_reduced _ e u).mpr hu
  have he' : (M.reindex e).toCoxeterSystem.IsReduced (u.map e) :=
    (system_reduced_iff _ _).mpr he
  rw [hM] at he'
  have hh := (Geometric.restriction_reduced_iff N (Set.range f) (u.map e)).mpr he'
  simpa only [List.map_map, e, Equiv.ofInjective_apply, Function.comp_def] using hh

end HarmonicArtin.CoxeterExchange

end OAI
