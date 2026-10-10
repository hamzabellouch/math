import Mathlib
import OAI.Topology.ArtinGroups.Quivers.CornerPath
import OAI.Topology.ArtinGroups.Complexes.HomSpace

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
variable {I J : Type*} [Fintype I] [Fintype J]

abbrev HomPath (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    (n v : ℤ) :=
  {t : I × J × Path V A //
    Path.source Q t.2.2 = (E.placement t.1).color ∧
    Path.target Q t.2.2 = (F.placement t.2.1).color ∧
    (F.placement t.2.1).cochain = (E.placement t.1).cochain + n ∧
    Path.length t.2.2 = v + (E.placement t.1).internal - (F.placement t.2.1).internal}

omit [Fintype V] [DecidableEq A] in
lemma homPath_of_coordinate_ne_zero (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n v : ℤ) (f : homSpace Q E F n v)
    (i : I) (j : J) (p : Path V A) (hp : pathCoordinates Q (f.val i j) p ≠ 0) :
    Path.source Q p = (E.placement i).color ∧ Path.target Q p = (F.placement j).color ∧
    (F.placement j).cochain = (E.placement i).cochain+n ∧
    Path.length p = v+(E.placement i).internal-(F.placement j).internal := by
  have hc := coordinates_corner Q (f.property.1.1 i j) (f.property.1.2 i j) hp
  refine ⟨hc.1, hc.2, ?_, ?_⟩
  · by_contra hh
    exact hp (by rw [(f.property.2 i j).1 hh, coordinates_zero])
  · by_contra hh
    exact hp ((coordinates_homogeneous Q _ _).mp (f.property.2 i j).2 p hh)

noncomputable def homPathBasis [DecidableEq I] [DecidableEq J]
    (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    (n v : ℤ) (t : HomPath Q E F n v) : homSpace Q E F n v :=
  ⟨Matrix.single t.val.1 t.val.2.1 (pathBasis Q t.val.2.2), by
    constructor
    · apply projectiveEntries_single Q
      · simpa only [t.property.1] using pathBasis_left Q (K := K) t.val.2.2
      · simpa only [t.property.2.1] using pathBasis_right Q (K := K) t.val.2.2
    · apply mapDegree_single Q _ _ _ _ _ _ _ t.property.2.2.1
      simpa only [t.property.2.2.2] using pathBasis_homogeneous Q (K := K) t.val.2.2⟩

noncomputable def homCoordinates (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n v : ℤ) :
    homSpace Q E F n v →ₗ[K] (HomPath Q E F n v → K) where
  toFun f t := pathCoordinates Q (f.val t.val.1 t.val.2.1) t.val.2.2
  map_add' f g := by
    funext t
    exact congrFun ((pathCoordinates Q).map_add (f.val t.val.1 t.val.2.1) (g.val t.val.1 t.val.2.1)) t.val.2.2
  map_smul' c f := by
    funext t
    exact (pathCoordinates Q).map_smul c (f.val t.val.1 t.val.2.1) |> congrFun <| t.val.2.2

omit [Fintype V] [DecidableEq A] in
lemma homCoordinates_injective (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n v : ℤ) : Function.Injective (homCoordinates Q E F n v) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro f hf
  change f = 0
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  apply (pathCoordinates Q).injective
  funext p
  change pathCoordinates Q (f.val i j) p = pathCoordinates Q 0 p
  rw [coordinates_zero]
  by_contra hp
  let t : HomPath Q E F n v := ⟨(i,j,p), homPath_of_coordinate_ne_zero Q E F n v f i j p hp⟩
  have hh := congrFun hf t
  dsimp only [homCoordinates, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, t] at hh
  exact hp hh

lemma homPathBasis_coordinates [DecidableEq I] [DecidableEq J]
    (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    (n v : ℤ) (s t : HomPath Q E F n v) :
    homCoordinates Q E F n v (homPathBasis Q E F n v s) t = if s=t then 1 else 0 := by
  classical
  dsimp only [homCoordinates, homPathBasis, LinearMap.coe_mk, AddHom.coe_mk]
  change pathCoordinates Q (Matrix.single s.val.1 s.val.2.1 (pathBasis Q (K := K) s.val.2.2)
    t.val.1 t.val.2.1) t.val.2.2 = _
  by_cases hi : s.val.1=t.val.1
  · by_cases hj : s.val.2.1=t.val.2.1
    · rw [hi, hj, Matrix.single_apply_same, pathBasis_coordinates]
      congr 1
      apply propext
      constructor
      · intro hp
        apply Subtype.ext
        exact Prod.ext hi (Prod.ext hj hp)
      · intro h
        exact congrArg (fun x : HomPath Q E F n v => x.val.2.2) h
    · have hs : s ≠ t := fun h => hj (congrArg (fun x : HomPath Q E F n v => x.val.2.1) h)
      simp only [Matrix.single_apply, hi, true_and, ite_eq_right hj, coordinates_zero,
        ite_eq_right hs]
  · have hs : s ≠ t := fun h => hi (congrArg (fun x : HomPath Q E F n v => x.val.1) h)
    simp only [Matrix.single_apply, hi, false_and, ite_false, coordinates_zero, ite_eq_right hs]

lemma homCoordinates_surjective (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n v : ℤ) : Function.Surjective (homCoordinates Q E F n v) := by
  classical
  intro f
  refine ⟨∑ t, f t • homPathBasis Q E F n v t, ?_⟩
  ext t
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    homPathBasis_coordinates]
  simp

noncomputable def homCoordinatesEquiv (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n v : ℤ) :
    homSpace Q E F n v ≃ₗ[K] (HomPath Q E F n v → K) :=
  LinearEquiv.ofBijective (homCoordinates Q E F n v)
    ⟨homCoordinates_injective Q E F n v, homCoordinates_surjective Q E F n v⟩

lemma homSpace_finrank (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n v : ℤ) :
    Module.finrank K (homSpace Q E F n v) = Nat.card (HomPath Q E F n v) := by
  classical
  rw [(homCoordinatesEquiv Q E F n v).finrank_eq, Module.finrank_pi, Nat.card_eq_fintype_card]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
