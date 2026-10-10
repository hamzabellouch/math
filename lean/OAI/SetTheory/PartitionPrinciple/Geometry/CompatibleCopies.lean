import OAI.SetTheory.PartitionPrinciple.Transfinite.AmalgamationCoinitiality

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps.CompatibleCopies

universe u v

structure Data {A : Type u} (P : MeetOrder A) (I : Type v) where
  top : A
  greatest : ∀ x, P.le x top
  anchor : I → I → A
  change : I → I → MeetIso P P
  self_anchor : ∀ i, anchor i i = top
  self_change : ∀ i x, (change i i).toFun x = x
  reverse : ∀ i j x, (change j i).toFun ((change i j).toFun x) = x
  anchor_change : ∀ i j, (change i j).toFun (anchor i j) = anchor j i
  triangle_domain : ∀ i j k, i ≠ j → j ≠ k → i ≠ k → ∀ x, P.le x (anchor i j) →
    (P.le ((change i j).toFun x) (anchor j k) ↔ P.le x (anchor i k))
  triangle_change : ∀ i j k, i ≠ j → j ≠ k → i ≠ k → ∀ x,
    P.le x (anchor i j) → P.le x (anchor i k) →
    (change j k).toFun ((change i j).toFun x) = (change i k).toFun x

namespace Data

variable {A : Type u} {I : Type v} {P : MeetOrder A} (d : Data P I)

theorem change_anchor_bound (i j : I) (x : A) (h : P.le x (d.anchor i j)) :
    P.le ((d.change i j).toFun x) (d.anchor j i) := by
  rw [← d.anchor_change i j]
  exact ((d.change i j).le_iff _ _).mpr h

theorem domain (i j k : I) (x : A) (h : P.le x (d.anchor i j)) :
    P.le ((d.change i j).toFun x) (d.anchor j k) ↔ P.le x (d.anchor i k) := by
  classical
  by_cases ij : i = j
  · subst j
    rw [d.self_change]
  · by_cases jk : j = k
    · subst k
      rw [d.self_anchor]
      exact ⟨fun _ => h, fun _ => d.greatest _⟩
    · by_cases ik : i = k
      · subst k
        rw [d.self_anchor]
        exact ⟨fun _ => d.greatest _, fun _ => d.change_anchor_bound i j x h⟩
      · exact d.triangle_domain i j k ij jk ik x h

theorem cocycle (i j k : I) (x : A)
    (hij : P.le x (d.anchor i j)) (hik : P.le x (d.anchor i k)) :
    (d.change j k).toFun ((d.change i j).toFun x) = (d.change i k).toFun x := by
  classical
  by_cases ij : i = j
  · subst j
    rw [d.self_change]
  · by_cases jk : j = k
    · subst k
      rw [d.self_change]
    · by_cases ik : i = k
      · subst k
        rw [d.reverse, d.self_change]
      · exact d.triangle_change i j k ij jk ik x hij hik

def Label (_d : Data P I) := I × A

def Related (x y : d.Label) : Prop :=
  P.le x.2 (d.anchor x.1 y.1) ∧ (d.change x.1 y.1).toFun x.2 = y.2

theorem related_refl (x : d.Label) : d.Related x x := by
  constructor
  · rw [d.self_anchor]
    exact d.greatest _
  · exact d.self_change _ _

theorem related_symm {x y : d.Label} (h : d.Related x y) : d.Related y x := by
  constructor
  · rw [← h.2]
    exact d.change_anchor_bound _ _ _ h.1
  · rw [← h.2, d.reverse]

theorem related_trans {x y z : d.Label} (hxy : d.Related x y) (hyz : d.Related y z) :
    d.Related x z := by
  have changed : P.le ((d.change x.1 y.1).toFun x.2) (d.anchor y.1 z.1) := by
    rw [hxy.2]
    exact hyz.1
  have hxz := (d.domain x.1 y.1 z.1 x.2 hxy.1).mp changed
  refine ⟨hxz, ?_⟩
  rw [← d.cocycle x.1 y.1 z.1 x.2 hxy.1 hxz, hxy.2]
  exact hyz.2

def setoid : Setoid d.Label where
  r := d.Related
  iseqv := ⟨d.related_refl, d.related_symm, d.related_trans⟩

def Le (x y : d.Label) : Prop :=
  P.le x.2 (d.anchor x.1 y.1) ∧ P.le ((d.change x.1 y.1).toFun x.2) y.2

theorem le_refl (x : d.Label) : d.Le x x :=
  ⟨(d.related_refl x).1, (d.self_change _ _).symm ▸ P.refl x.2⟩

theorem related_le {x y : d.Label} (h : d.Related x y) : d.Le x y :=
  ⟨h.1, h.2.symm ▸ P.refl y.2⟩

theorem le_trans {x y z : d.Label} (hxy : d.Le x y) (hyz : d.Le y z) : d.Le x z := by
  have changed := P.trans hxy.2 hyz.1
  have hxz := (d.domain x.1 y.1 z.1 x.2 hxy.1).mp changed
  refine ⟨hxz, ?_⟩
  rw [← d.cocycle x.1 y.1 z.1 x.2 hxy.1 hxz]
  exact P.trans (((d.change y.1 z.1).le_iff _ _).mpr hxy.2) hyz.2

theorem le_antisymm_related {x y : d.Label} (hxy : d.Le x y) (hyx : d.Le y x) :
    d.Related x y := by
  refine ⟨hxy.1, P.antisymm hxy.2 ?_⟩
  have lower := ((d.change x.1 y.1).le_iff _ _).mpr hyx.2
  rw [d.reverse] at lower
  exact lower

theorem same_vertex_le (i : I) (x y : A) : d.Le (i, x) (i, y) ↔ P.le x y := by
  constructor
  · intro h
    simpa only [d.self_change] using h.2
  · intro h
    exact ⟨(d.self_anchor i).symm ▸ d.greatest x, (d.self_change i x).symm ▸ h⟩

def part (i j : I) (y : A) : A := (d.change j i).toFun (P.meet y (d.anchor j i))

theorem part_anchor (i j : I) (y : A) : P.le (d.part i j y) (d.anchor i j) :=
  d.change_anchor_bound j i _ (P.meet_le_right _ _)

theorem part_below (i j : I) (y : A) : d.Le (i, d.part i j y) (j, y) := by
  refine ⟨d.part_anchor i j y, ?_⟩
  change P.le ((d.change i j).toFun ((d.change j i).toFun _)) y
  rw [d.reverse]
  exact P.meet_le_left _ _

theorem below_iff_part (i j : I) (x y : A) : d.Le (i, x) (j, y) ↔ P.le x (d.part i j y) := by
  constructor
  · intro h
    have lower := ((d.change j i).le_iff _ _).mpr
      (P.le_meet h.2 (d.change_anchor_bound i j x h.1))
    rw [d.reverse] at lower
    exact lower
  · intro h
    exact d.le_trans ((d.same_vertex_le i _ _).mpr h) (d.part_below i j y)

theorem move_to_upper_vertex {x y : d.Label} (lower : d.Le x y) :
    d.Related x (y.1, (d.change x.1 y.1).toFun x.2) ∧
      P.le ((d.change x.1 y.1).toFun x.2) y.2 :=
  ⟨⟨lower.1, rfl⟩, lower.2⟩

end Data
end PartitionPilot.Compression.RecursiveMaps.CompatibleCopies

end

end OAI
