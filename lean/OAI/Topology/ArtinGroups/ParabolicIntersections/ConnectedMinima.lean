import Mathlib

namespace OAI

/-!
# Lowering paths across tied heights

This is the finite-path argument of §6.5 of paper 082-03. The local
hypotheses are precisely the connected descending neighborhoods and the
compatibility across tied adjacent vertices. They are not installed as
published assumptions; their verification for the relative harmonic
height is a separate part of that paper's proof.
-/

namespace HarmonicArtin.ParabolicIntersections

section Paths

variable {V H : Type*} [LinearOrder H]
variable (adj : V → V → Prop) (height : V → H)

/-- Paths all of whose edges and vertices lie in a specified region.
For the reflexive path the endpoint condition is supplied separately. -/
def PathWithin (p : V → Prop) (a b : V) : Prop :=
  Relation.ReflTransGen (fun x y => p x ∧ p y ∧ adj x y) a b

private theorem path_mono {p q : V → Prop} (hpq : ∀ v, p v → q v)
    {a b : V} (h : PathWithin adj p a b) : PathWithin adj q a b :=
  by
    induction h with
    | refl => exact .refl
    | tail _ he ih => exact ih.tail ⟨hpq _ he.1, hpq _ he.2.1, he.2.2⟩

/-- Descending neighbors at one vertex lie in one strict-sublevel
component; a tied edge carries that component to the other vertex. -/
structure LocalDescent : Prop where
  symmetric : ∀ {a b}, adj a b → adj b a
  descending : ∀ v a b, adj v a → height a < height v →
    adj v b → height b < height v →
    PathWithin adj (fun z => height z < height v) a b
  tied : ∀ v w, adj v w → height v = height w →
    ∀ a, adj v a → height a < height v →
    ∃ b, adj w b ∧ height b < height w ∧
      PathWithin adj (fun z => height z < height v) a b

/-- Remove all occurrences of one maximal height in a finite path.
The invariant also covers a whole segment of tied vertices. -/
theorem lower_path (D : LocalDescent adj height) (h : H)
    {a b : V} (ha : height a < h) (hb : height b < h)
    (p : PathWithin adj (fun v => height v ≤ h) a b) :
    PathWithin adj (fun v => height v < h) a b := by
  have step : ∀ {v}, PathWithin adj (fun z => height z ≤ h) a v →
      (height v < h ∧ PathWithin adj (fun z => height z < h) a v) ∨
      (height v = h ∧ ∃ c, adj v c ∧ height c < h ∧
        PathWithin adj (fun z => height z < h) a c) := by
    intro v hv
    induction hv with
    | refl => exact Or.inl ⟨ha, .refl⟩
    | @tail v w p edge ih =>
      obtain ⟨_, hw, hvw⟩ := edge
      by_cases hwl : height w < h
      · left
        refine ⟨hwl, ?_⟩
        rcases ih with ⟨hvl, pav⟩ | ⟨hve, c, hvc, hcl, pac⟩
        · exact pav.tail ⟨hvl, hwl, hvw⟩
        · have pcw := D.descending v c w hvc (hve ▸ hcl) hvw (hve ▸ hwl)
          rw [hve] at pcw
          exact pac.trans pcw
      · right
        have hwe : height w = h := le_antisymm hw (le_of_not_gt hwl)
        refine ⟨hwe, ?_⟩
        rcases ih with ⟨hvl, pav⟩ | ⟨hve, c, hvc, hcl, pac⟩
        · exact ⟨v, D.symmetric hvw, hvl, pav⟩
        · obtain ⟨d, hwd, hdl, pcd⟩ := D.tied v w hvw (hve.trans hwe.symm)
            c hvc (hve ▸ hcl)
          rw [hve] at pcd
          exact ⟨d, hwd, hwe ▸ hdl, pac.trans pcd⟩
  rcases step p with ⟨_, hp⟩ | ⟨he, _⟩
  · exact hp
  · exact (ne_of_lt hb he).elim

private theorem bounded_path {a b : V} (p : Relation.ReflTransGen adj a b) :
    ∃ h, height a ≤ h ∧ PathWithin adj (fun v => height v ≤ h) a b := by
  induction p with
  | refl => exact ⟨height a, le_rfl, .refl⟩
  | @tail v w p edge ih =>
    obtain ⟨h, ha, hp⟩ := ih
    refine ⟨max h (height w), ha.trans (le_max_left _ _), ?_⟩
    have hv : height v ≤ max h (height w) := by
      rcases hp.cases_tail with rfl | ⟨u, _, _, hv, _⟩
      · exact ha.trans (le_max_left _ _)
      · exact hv.trans (le_max_left _ _)
    exact (path_mono adj (fun _ hv => hv.trans (le_max_left _ _)) hp).tail
      ⟨hv, le_max_right _ _, edge⟩

private theorem strictly_bounded_path (h : H) {a b : V} (ha : height a < h)
    (p : PathWithin adj (fun v => height v < h) a b) :
    ∃ k, k < h ∧ height a ≤ k ∧ PathWithin adj (fun v => height v ≤ k) a b := by
  induction p with
  | refl => exact ⟨height a, ha, le_rfl, .refl⟩
  | @tail v w p edge ih =>
    obtain ⟨k, hk, hak, pk⟩ := ih
    obtain ⟨_, hw, hvw⟩ := edge
    refine ⟨max k (height w), max_lt hk hw, hak.trans (le_max_left _ _), ?_⟩
    have hvk : height v ≤ k := by
      rcases pk.cases_tail with rfl | ⟨u, _, _, hvk, _⟩
      · exact hak
      · exact hvk
    exact (path_mono adj (fun _ hz => hz.trans (le_max_left _ _)) pk).tail
      ⟨hvk.trans (le_max_left _ _), le_max_right _ _, hvw⟩

/-- Every sublevel of a well-founded height with the two local descent
properties contains a path between any of its vertices that were connected
in the original graph. -/
theorem sublevel_path (D : LocalDescent adj height)
    (wf : WellFounded ((· < ·) : H → H → Prop)) (c : H)
    {a b : V} (ha : height a ≤ c) (hb : height b ≤ c)
    (p : Relation.ReflTransGen adj a b) :
    PathWithin adj (fun v => height v ≤ c) a b := by
  obtain ⟨h, hbound, hp⟩ := bounded_path adj height p
  clear hbound
  induction h using wf.induction with
  | h h ih =>
    by_cases hc : h ≤ c
    · exact path_mono adj (fun _ hv => hv.trans hc) hp
    · have hch : c < h := lt_of_not_ge hc
      have pl := lower_path adj height D h (ha.trans_lt hch) (hb.trans_lt hch) hp
      obtain ⟨k, hk, _, pk⟩ := strictly_bounded_path adj height h (ha.trans_lt hch) pl
      exact ih k hk pk

/-- The minimum-height vertices in a connected graph form a connected
subgraph. This is the path-lowering conclusion used in §6.5. -/
theorem minimum_path (D : LocalDescent adj height)
    (wf : WellFounded ((· < ·) : H → H → Prop))
    {a b : V} (ha : ∀ v, height a ≤ height v) (hb : ∀ v, height b ≤ height v)
    (p : Relation.ReflTransGen adj a b) :
    PathWithin adj (fun v => ∀ w, height v ≤ height w) a b := by
  have hp := sublevel_path adj height D wf (height a) le_rfl (hb a) p
  exact path_mono adj (fun v hv w => hv.trans (ha w)) hp

end Paths

end HarmonicArtin.ParabolicIntersections

end OAI
