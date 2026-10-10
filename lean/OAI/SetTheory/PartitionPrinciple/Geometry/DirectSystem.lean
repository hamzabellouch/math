import OAI.SetTheory.PartitionPrinciple.Transfinite.OrdinalExternalHeights

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps

universe u v

structure DirectSystem (I : Type u) [LinearOrder I] where
  Point : I → Type u
  map : ∀ {i j}, i ≤ j → Point i → Point j
  map_self : ∀ i x, map (le_refl i) x = x
  map_comp : ∀ {i j k} (hij : i ≤ j) (hjk : j ≤ k) x,
    map (le_trans hij hjk) x = map hjk (map hij x)
  injective : ∀ {i j} (h : i ≤ j), Function.Injective (map h)

namespace DirectSystem
variable {I : Type u} [LinearOrder I] (c : DirectSystem I)

def Label := (i : I) × c.Point i
def Related (x y : c.Label) : Prop :=
  ∃ (k : I) (hx : x.1 ≤ k) (hy : y.1 ≤ k), c.map hx x.2 = c.map hy y.2

theorem related_refl (x : c.Label) : c.Related x x := ⟨x.1, le_rfl, le_rfl, rfl⟩
theorem related_symm {x y : c.Label} (h : c.Related x y) : c.Related y x := by
  rcases h with ⟨k, hx, hy, eq⟩
  exact ⟨k, hy, hx, eq.symm⟩

theorem related_trans {x y z : c.Label} (hxy : c.Related x y) (hyz : c.Related y z) :
    c.Related x z := by
  rcases hxy with ⟨k, hx, hy, eq1⟩
  rcases hyz with ⟨l, hy', hz, eq2⟩
  refine ⟨max k l, le_trans hx (le_max_left _ _), le_trans hz (le_max_right _ _), ?_⟩
  calc
    c.map _ x.2 = c.map (le_max_left k l) (c.map hx x.2) := c.map_comp _ _ _
    _ = c.map (le_max_left k l) (c.map hy y.2) := congrArg _ eq1
    _ = c.map (le_max_right k l) (c.map hy' y.2) :=
      (c.map_comp _ _ _).symm.trans (c.map_comp _ _ _)
    _ = c.map (le_max_right k l) (c.map hz z.2) := congrArg _ eq2
    _ = c.map _ z.2 := (c.map_comp _ _ _).symm

def setoid : Setoid c.Label := ⟨c.Related, c.related_refl, c.related_symm, c.related_trans⟩
def Union := Quotient c.setoid
def point (i : I) (x : c.Point i) : c.Union := Quotient.mk c.setoid ⟨i, x⟩

theorem point_map {i j : I} (h : i ≤ j) (x : c.Point i) :
    c.point j (c.map h x) = c.point i x := by
  apply Quotient.sound
  exact ⟨j, le_rfl, h, c.map_self _ _⟩

theorem point_injective (i : I) : Function.Injective (c.point i) := by
  intro x y eq
  rcases Quotient.exact eq with ⟨k, hx, hy, same⟩
  exact c.injective hx same

theorem cover (x : c.Union) : ∃ i a, c.point i a = x := by
  induction x using Quotient.ind with
  | _ x => exact ⟨x.1, x.2, rfl⟩

theorem pair_cover (d : DirectSystem I) (x : c.Union) (y : d.Union) :
    ∃ i a b, c.point i a = x ∧ d.point i b = y := by
  rcases c.cover x with ⟨i, a, rfl⟩
  rcases d.cover y with ⟨j, b, rfl⟩
  exact ⟨max i j, c.map (le_max_left _ _) a, d.map (le_max_right _ _) b,
    c.point_map _ _, d.point_map _ _⟩

theorem triple_cover (d e : DirectSystem I) (x : c.Union) (y : d.Union) (z : e.Union) :
    ∃ i a b t, c.point i a = x ∧ d.point i b = y ∧ e.point i t = z := by
  rcases c.pair_cover d x y with ⟨i, a, b, rfl, rfl⟩
  rcases e.cover z with ⟨j, t, rfl⟩
  exact ⟨max i j, c.map (le_max_left _ _) a, d.map (le_max_left _ _) b,
    e.map (le_max_right _ _) t, c.point_map _ _, d.point_map _ _, e.point_map _ _⟩

def descend {H : Type v} (value : ∀ i, c.Point i → H)
    (coherent : ∀ {i j} (h : i ≤ j) x, value j (c.map h x) = value i x) : c.Union → H :=
  Quotient.lift (fun x => value x.1 x.2) (by
    intro x y related
    rcases related with ⟨k, hx, hy, eq⟩
    exact (coherent hx x.2).symm.trans ((congrArg (value k) eq).trans (coherent hy y.2)))

theorem descend_point {H : Type v} (value : ∀ i, c.Point i → H)
    (coherent : ∀ {i j} (h : i ≤ j) x, value j (c.map h x) = value i x) (i : I) (x : c.Point i) :
    c.descend value coherent (c.point i x) = value i x := rfl

section Binary
variable (d e : DirectSystem I) (op : ∀ i, c.Point i → d.Point i → e.Point i)
    (coherent : ∀ {i j} (h : i ≤ j) x y,
      e.map h (op i x y) = op j (c.map h x) (d.map h y))

def binaryLabel (x : c.Label) (y : d.Label) : e.Union :=
  e.point (max x.1 y.1)
    (op _ (c.map (le_max_left _ _) x.2) (d.map (le_max_right _ _) y.2))

include coherent

theorem binaryLabel_at (x : c.Label) (y : d.Label) (k : I) (hx : x.1 ≤ k) (hy : y.1 ≤ k) :
    c.binaryLabel d e op x y = e.point k (op k (c.map hx x.2) (d.map hy y.2)) := by
  let h : max x.1 y.1 ≤ k := max_le hx hy
  change e.point (max x.1 y.1) _ = _
  rw [← e.point_map h, coherent, ← c.map_comp, ← d.map_comp]

theorem binaryLabel_respects (x x' : c.Label) (y y' : d.Label)
    (eqx : c.Related x x') (eqy : d.Related y y') :
    c.binaryLabel d e op x y = c.binaryLabel d e op x' y' := by
  rcases eqx with ⟨k, hx, hx', eqx⟩
  rcases eqy with ⟨l, hy, hy', eqy⟩
  rw [c.binaryLabel_at d e op coherent x y (max k l)
    (le_trans hx (le_max_left _ _)) (le_trans hy (le_max_right _ _)),
    c.binaryLabel_at d e op coherent x' y' (max k l)
    (le_trans hx' (le_max_left _ _)) (le_trans hy' (le_max_right _ _))]
  rw [c.map_comp hx (le_max_left _ _), c.map_comp hx' (le_max_left _ _),
    d.map_comp hy (le_max_right _ _), d.map_comp hy' (le_max_right _ _), eqx, eqy]

def binary : c.Union → d.Union → e.Union :=
  Quotient.lift₂ (c.binaryLabel d e op)
    (fun x y x' y' hx hy => c.binaryLabel_respects d e op coherent x x' y y' hx hy)

theorem binary_point (i : I) (x : c.Point i) (y : d.Point i) :
    c.binary d e op coherent (c.point i x) (d.point i y) = e.point i (op i x y) := by
  change c.binaryLabel d e op ⟨i, x⟩ ⟨i, y⟩ = _
  erw [c.binaryLabel_at d e op coherent _ _ i le_rfl le_rfl, c.map_self, d.map_self]

end Binary

end DirectSystem
end PartitionPilot.Compression.RecursiveMaps

end

end OAI
