import OAI.SetTheory.PartitionPrinciple.Geometry.TileTreeGluing

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps.RootedGluing.Scheme

universe u
variable {V : Type u} (d : Scheme V)

def Label := (v : V) × d.Space v

inductive Related : d.Label → d.Label → Prop
  | parent (v : V) (h : d.depth v ≠ 0)
      (x : {x : d.Space v // (d.order v).le x (d.childAnchor v h)}) :
      Related ⟨v, x.val⟩ ⟨d.parent v, ((d.link v h).toFun x).val⟩
  | refl (x) : Related x x
  | symm {x y} : Related x y → Related y x
  | trans {x y z} : Related x y → Related y z → Related x z

def labelSetoid : Setoid d.Label := ⟨d.Related, Related.refl, Related.symm, Related.trans⟩
def Generated := Quotient d.labelSetoid
def labelClass (v : V) (x : d.Space v) : d.Generated := Quotient.mk d.labelSetoid ⟨v, x⟩

theorem label_parent (v : V) (h : d.depth v ≠ 0)
    (x : {x : d.Space v // (d.order v).le x (d.childAnchor v h)}) :
    d.labelClass v x.val = d.labelClass (d.parent v) ((d.link v h).toFun x).val :=
  Quotient.sound (Related.parent v h x)

noncomputable def stageClass : (n : Nat) → (d.stages n).Point → d.Generated
  | 0, x => d.labelClass d.root x
  | n + 1, .inl x => stageClass n x
  | _ + 1, .inr x => d.labelClass x.1.val x.2.val

theorem stageClass_old (n : Nat) (x : (d.stages n).Point) :
    d.stageClass (n + 1) ((d.stages n).batch.old.toFun x) = d.stageClass n x := rfl

theorem stageClass_vertex (n : Nat) (v : V) (hv : d.depth v ≤ n) (x : d.Space v) :
    d.stageClass n (((d.stages n).vertex v hv).toFun x) = d.labelClass v x := by
  classical
  induction n generalizing v with
  | zero =>
    have eq := d.zero_eq_root v (Nat.eq_zero_of_le_zero hv)
    subst v
    rfl
  | succ n ih =>
    change d.stageClass (n + 1) (((d.stages n).successor.vertex v hv).toFun x) = _
    by_cases older : d.depth v ≤ n
    · rw [(d.stages n).successor_old v older x, d.stageClass_old]
      exact ih v older x
    · let s := d.stages n
      let i : s.Layer := ⟨v, by omega⟩
      rw [s.successor_new i x]
      by_cases base : (d.order v).le x (d.childAnchor v (s.layer_nonzero i))
      · have eq : (s.batch.tile i).toFun x =
            s.batch.old.toFun ((s.vertex (d.parent v) (s.parent_present i)).toFun
              ((d.link v (s.layer_nonzero i)).toFun ⟨x, base⟩).val) :=
          (s.batch.tile_old_overlap i x _).mpr ⟨base, rfl⟩
        rw [eq, d.stageClass_old]
        exact (ih (d.parent v) (s.parent_present i) _).trans
          (d.label_parent v (s.layer_nonzero i) ⟨x, base⟩).symm
      · have represented := (s.batch.glue i).represent_new x base
        change d.stageClass (n + 1) (s.batch.componentMap i ((s.batch.glue i).represent x)) = _
        rw [represented]
        rfl

theorem stageClass_up {n m : Nat} (h : n ≤ m) (x : (d.stages n).Point) :
    d.stageClass m (d.chain.up h x) = d.stageClass n x := by
  induction h with
  | refl => erw [d.chain.up_self]
  | @step m h ih =>
    erw [d.chain.up_succ h]
    exact (d.stageClass_old m _).trans ih

noncomputable def toGenerated : d.Node → d.Generated :=
  Quotient.lift (fun x => d.stageClass x.1 x.2) (by
    rintro x y ⟨k, hx, hy, eq⟩
    exact (d.stageClass_up hx x.2).symm.trans
      ((congrArg (d.stageClass k) eq).trans (d.stageClass_up hy y.2)))

theorem toGenerated_vertex (v : V) (x : d.Space v) :
    d.toGenerated ((d.vertex v).toFun x) = d.labelClass v x :=
  d.stageClass_vertex (d.depth v) v (le_refl _) x

theorem related_sound {x y : d.Label} (h : d.Related x y) :
    (d.vertex x.1).toFun x.2 = (d.vertex y.1).toFun y.2 := by
  induction h with
  | parent v hv x => exact d.parent_identification v hv x
  | refl => rfl
  | symm h ih => exact ih.symm
  | trans h1 h2 ih1 ih2 => exact ih1.trans ih2

theorem exact_identifications (v w : V) (x : d.Space v) (y : d.Space w) :
    (d.vertex v).toFun x = (d.vertex w).toFun y ↔ d.Related ⟨v, x⟩ ⟨w, y⟩ := by
  constructor
  · intro eq
    have classes := congrArg d.toGenerated eq
    rw [d.toGenerated_vertex, d.toGenerated_vertex] at classes
    exact Quotient.exact classes
  · exact d.related_sound

noncomputable def fromGenerated : d.Generated → d.Node :=
  Quotient.lift (fun x => (d.vertex x.1).toFun x.2) (fun _ _ h => d.related_sound h)

theorem from_to (x : d.Node) : d.fromGenerated (d.toGenerated x) = x := by
  rcases d.cover x with ⟨v, a, rfl⟩
  rw [d.toGenerated_vertex]
  rfl

theorem to_from (x : d.Generated) : d.toGenerated (d.fromGenerated x) = x := by
  induction x using Quotient.ind with
  | _ x => exact d.toGenerated_vertex x.1 x.2

end PartitionPilot.Compression.RecursiveMaps.RootedGluing.Scheme

end

end OAI
