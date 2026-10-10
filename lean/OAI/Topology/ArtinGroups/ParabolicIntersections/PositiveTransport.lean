import OAI.Topology.ArtinGroups.Cancellation.SphericalPositiveCancelLeft

namespace OAI

/-! Relabeling positive Artin monoids and finite-type cancellation. -/
namespace HarmonicArtin.ParabolicIntersections
open CoxeterExchange Geometric
attribute [local instance] Classical.decEq Classical.propDecidable

private lemma altList_map {S T : Type} (f : S → T) (i j : S) (n : ℕ) :
    (altList i j n).map f = altList (f i) (f j) n := by
  induction n generalizing i j with
  | zero => rfl
  | succ n ih => simp only [altList_succ, List.map_cons, ih]

variable {S T : Type} (M : CoxeterMatrix S) (N : CoxeterMatrix T)
    (f : S → T) (hf : ∀ i j, N (f i) (f j)=M i j)

include hf in
private lemma positiveMap_relations :
    ∀ a b : FreeMonoid S, positiveBraidRelations M a b →
      FreeMonoid.lift (fun s => positiveGenerator N (f s)) a =
      FreeMonoid.lift (fun s => positiveGenerator N (f s)) b := by
  rintro a b ⟨i,j,rfl,rfl⟩
  simp only [FreeMonoid.lift_ofList]
  have h := wordPositive_braid N (f i) (f j)
  rw [hf] at h
  have hm : wordPositive N ((altList i j (M i j)).map f) =
      wordPositive N ((altList j i (M i j)).map f) := by
    simpa only [altList_map] using h
  simpa only [wordPositive,List.map_map,Function.comp_def] using hm

noncomputable def positiveMap : PositiveArtin M →* PositiveArtin N :=
  PresentedMonoid.lift (fun s => positiveGenerator N (f s)) (positiveMap_relations M N f hf)

@[simp] lemma positiveMap_generator (i : S) :
    positiveMap M N f hf (positiveGenerator M i)=positiveGenerator N (f i) := rfl

lemma positiveMap_word (w : List S) :
    positiveMap M N f hf (wordPositive M w)=wordPositive N (w.map f) := by
  simp only [wordPositive,map_list_prod,List.map_map,Function.comp_def,positiveMap_generator]

lemma positiveMap_prefix {a b : PositiveArtin M} (h : PositivePrefix M a b) :
    PositivePrefix N (positiveMap M N f hf a) (positiveMap M N f hf b) := by
  obtain ⟨c,rfl⟩ := h
  exact ⟨_,map_mul _ _ _⟩

/-- Cancellation in a finite Coxeter type, without an artificial subtype
of generators in the statement. -/
theorem finite_positive_cancel_left [Fintype S] [LinearOrder S] [Finite M.Group]
    (a b c : PositiveArtin M) (h : a*b=a*c) : b=c := by
  let R := restrictedMatrix M Set.univ
  let f : S → (Set.univ : Set S) := fun s => ⟨s,Set.mem_univ s⟩
  let up := positiveMap M R f (fun _ _ => rfl)
  let down := positiveMap R M Subtype.val (fun _ _ => rfl)
  have inverse : ∀ x, down (up x)=x := by
    intro x
    obtain ⟨w,rfl⟩ := positive_word_surjective M x
    calc
      down (up (wordPositive M w)) = down (wordPositive R (w.map f)) :=
        congrArg down (positiveMap_word M R f (fun _ _ => rfl) w)
      _ = wordPositive M ((w.map f).map Subtype.val) :=
        positiveMap_word R M Subtype.val (fun _ _ => rfl) (w.map f)
      _ = wordPositive M w := by
        rw [List.map_map]
        change wordPositive M (w.map id)=wordPositive M w
        rw [List.map_id]
  have hs : IsSpherical M Set.univ := by
    change Finite (coxeterParabolic M Set.univ)
    infer_instance
  have he : up b=up c := spherical_positive_cancel_left M Set.univ hs (up a) (up b) (up c)
    (by simpa only [←map_mul] using congrArg up h)
  simpa only [inverse] using congrArg down he

end HarmonicArtin.ParabolicIntersections

end OAI
