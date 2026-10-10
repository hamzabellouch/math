import OAI.SetTheory.PartitionPrinciple.Geometry.TileTreeGluing

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps.RootedGluing.Scheme

open Attachment
universe u
variable {V : Type u} (d : Scheme V)

def Supports (v : V) (x : d.Node) : Prop := ∃ a, (d.vertex v).toFun a = x

def LeastSupport (v : V) (x : d.Node) : Prop :=
  d.Supports v x ∧ ∀ w, d.Supports w x → d.depth v ≤ d.depth w

theorem fresh_stage_vertex (n : Nat) (x : (d.stages n).batch.Fresh)
    (w : V) (hw : d.depth w ≤ n + 1) (a : d.Space w)
    (eq : ((d.stages (n + 1)).vertex w hw).toFun a = Sum.inr x) :
    w = x.1.val := by
  classical
  let s := d.stages n
  change (s.successor.vertex w hw).toFun a = Sum.inr x at eq
  by_cases old : d.depth w ≤ n
  · rw [s.successor_old w old a] at eq
    exact False.elim (Sum.inl_ne_inr eq)
  · let i : s.Layer := ⟨w, by omega⟩
    rw [s.successor_new i a] at eq
    change s.batch.componentMap i ((s.batch.glue i).represent a) = Sum.inr x at eq
    by_cases base : (d.order w).le a (d.childAnchor w (s.layer_nonzero i))
    · rw [(s.batch.glue i).represent_old a base] at eq
      exact False.elim (Sum.inl_ne_inr eq)
    · rw [(s.batch.glue i).represent_new a base] at eq
      exact congrArg (fun z : s.batch.Fresh => z.1.val) (Sum.inr.inj eq)

theorem fresh_vertex_eq (v : V) (h : d.depth v ≠ 0) (a : d.Space v)
    (fresh : ¬ (d.order v).le a (d.childAnchor v h))
    (w : V) (hw : d.depth w ≤ d.depth v) (b : d.Space w)
    (eq : (d.vertex w).toFun b = (d.vertex v).toFun a) : w = v := by
  let n := d.depth (d.parent v)
  let s := d.stages n
  let i : s.Layer := ⟨v, (d.parent_depth v h).symm⟩
  let x : s.batch.Fresh := ⟨i, ⟨a, fresh⟩⟩
  have hv : (d.vertex v).toFun a = d.chain.point (n + 1) (Sum.inr x) := by
    rw [d.vertex_at v (n + 1) i.property.le a]
    change d.chain.point (n + 1) ((s.successor.vertex v i.property.le).toFun a) = _
    rw [s.successor_new i a]
    change d.chain.point (n + 1) (s.batch.componentMap i ((s.batch.glue i).represent a)) = _
    rw [(s.batch.glue i).represent_new a fresh]
    rfl
  have hw' : d.depth w ≤ n + 1 := hw.trans i.property.le
  have stageEq : ((d.stages (n + 1)).vertex w hw').toFun b = Sum.inr x := by
    apply d.chain.include_injective (n + 1)
    rw [← d.vertex_at w (n + 1) hw' b]
    exact eq.trans hv
  exact d.fresh_stage_vertex n x w hw' b stageEq

theorem supports_parent_iff (v : V) (h : d.depth v ≠ 0) (a : d.Space v) :
    d.Supports (d.parent v) ((d.vertex v).toFun a) ↔
      (d.order v).le a (d.childAnchor v h) := by
  constructor
  · rintro ⟨b, eq⟩
    by_contra fresh
    have smaller := d.parent_depth v h
    have same := d.fresh_vertex_eq v h a fresh (d.parent v) (by omega) b eq
    rw [same] at smaller
    omega
  · intro base
    exact ⟨((d.link v h).toFun ⟨a, base⟩).val,
      (d.parent_identification v h ⟨a, base⟩).symm⟩

theorem leastSupport_vertex_iff (v : V) (h : d.depth v ≠ 0) (a : d.Space v) :
    d.LeastSupport v ((d.vertex v).toFun a) ↔
      ¬ (d.order v).le a (d.childAnchor v h) := by
  constructor
  · intro least base
    have parent := least.2 (d.parent v) ((d.supports_parent_iff v h a).mpr base)
    have smaller := d.parent_depth v h
    omega
  · intro fresh
    refine ⟨⟨a, rfl⟩, ?_⟩
    rintro w ⟨b, eq⟩
    by_contra notle
    have same := d.fresh_vertex_eq v h a fresh w (by omega) b eq
    subst w
    exact notle (Nat.le_refl _)

theorem leastSupport_root_iff (x : d.Node) :
    d.LeastSupport d.root x ↔ d.Supports d.root x := by
  exact ⟨And.left, fun hx => ⟨hx, fun _ _ => by rw [d.depth_root]; exact Nat.zero_le _⟩⟩

theorem leastSupport_unique {v w : V} {x : d.Node}
    (first : d.LeastSupport v x) (second : d.LeastSupport w x) : v = w := by
  have sameDepth := Nat.le_antisymm (first.2 w second.1) (second.2 v first.1)
  by_cases zero : d.depth v = 0
  · exact (d.zero_eq_root v zero).trans (d.zero_eq_root w (sameDepth.symm.trans zero)).symm
  · rcases first.1 with ⟨a, rfl⟩
    rcases second.1 with ⟨b, eq⟩
    exact (d.fresh_vertex_eq v zero a ((d.leastSupport_vertex_iff v zero a).mp first)
      w sameDepth.symm.le b eq).symm

theorem existsUnique_leastSupport (x : d.Node) : ∃! v, d.LeastSupport v x := by
  classical
  have present : ∃ n, ∃ v, d.depth v = n ∧ d.Supports v x := by
    rcases d.cover x with ⟨v, a, eq⟩
    exact ⟨d.depth v, v, rfl, a, eq⟩
  rcases Nat.find_spec present with ⟨v, hv, support⟩
  have least : d.LeastSupport v x := by
    refine ⟨support, ?_⟩
    intro w hw
    rw [hv]
    exact Nat.find_min' present ⟨w, rfl, hw⟩
  exact ⟨v, least, fun w hw => d.leastSupport_unique hw least⟩

end PartitionPilot.Compression.RecursiveMaps.RootedGluing.Scheme

end

end OAI
