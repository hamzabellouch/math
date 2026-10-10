import OAI.SetTheory.PartitionPrinciple.Forcing.IdealChain

namespace OAI


namespace PartitionPilot.Compression.RecursiveMaps

namespace RootedGluing

open Attachment
universe u

def chainIso {A B C : Type u} {P : MeetOrder A} {Q : MeetOrder B} {R : MeetOrder C}
    (f : MeetIso P Q) (g : MeetIso Q R) : MeetIso P R where
  toMeetEmbedding := compose f.toMeetEmbedding g.toMeetEmbedding
  inverse x := f.inverse (g.inverse x)
  left_inverse x := by
    change f.inverse (g.inverse (g.toFun (f.toFun x))) = x
    rw [g.left_inverse, f.left_inverse]
  right_inverse x := by
    change g.toFun (f.toFun (f.inverse (g.inverse x))) = x
    rw [f.right_inverse, g.right_inverse]

structure Scheme (V : Type u) where
  root : V
  depth : V → Nat
  depth_root : depth root = 0
  zero_eq_root : ∀ v, depth v = 0 → v = root
  parent : V → V
  parent_depth : ∀ v, depth v ≠ 0 → depth (parent v) + 1 = depth v
  Space : V → Type u
  order : ∀ v, MeetOrder (Space v)
  childAnchor : ∀ v, depth v ≠ 0 → Space v
  parentAnchor : ∀ v, depth v ≠ 0 → Space (parent v)
  link : ∀ v h, MeetIso (idealOrder (order v) (childAnchor v h))
    (idealOrder (order (parent v)) (parentAnchor v h))

namespace Scheme
variable {V : Type u} (d : Scheme V)

structure Stage (n : Nat) where
  Point : Type u
  order : MeetOrder Point
  vertex : ∀ v, d.depth v ≤ n → IdealEmbedding (d.order v) order

noncomputable def initial : d.Stage 0 where
  Point := d.Space d.root
  order := d.order d.root
  vertex v hv := by
    have eq := d.zero_eq_root v (Nat.eq_zero_of_le_zero hv)
    subst v
    exact IdealEmbedding.identity _

namespace Stage
variable {d} {n : Nat} (s : d.Stage n)

def Layer (_s : d.Stage n) := {v : V // d.depth v = n + 1}

theorem layer_nonzero (v : s.Layer) : d.depth v.val ≠ 0 := by
  rw [v.property]
  exact Nat.succ_ne_zero n

theorem parent_present (v : s.Layer) : d.depth (d.parent v.val) ≤ n := by
  have h := d.parent_depth v.val (s.layer_nonzero v)
  rw [v.property] at h
  omega

noncomputable def batch : PrincipalBatch.Family s.order s.Layer where
  Space v := d.Space v.val
  order v := d.order v.val
  glue v := {
    leftAnchor := (s.vertex (d.parent v.val) (s.parent_present v)).toFun
      (d.parentAnchor v.val (s.layer_nonzero v))
    rightAnchor := d.childAnchor v.val (s.layer_nonzero v)
    overlap := chainIso (d.link v.val (s.layer_nonzero v))
      ((s.vertex (d.parent v.val) (s.parent_present v)).principalIso
        (d.parentAnchor v.val (s.layer_nonzero v))) }

noncomputable def successor : d.Stage (n + 1) := by
  classical
  exact {
    Point := s.batch.Node
    order := s.batch.extension
    vertex := fun v hv =>
      if old : d.depth v ≤ n then (s.vertex v old).comp s.batch.old
      else s.batch.tile ⟨v, by omega⟩ }

theorem successor_old (v : V) (hv : d.depth v ≤ n) (x : d.Space v) :
    (s.successor.vertex v (Nat.le_succ_of_le hv)).toFun x =
      s.batch.old.toFun ((s.vertex v hv).toFun x) := by
  dsimp only [successor]
  erw [dite_eq_left hv]
  rfl

theorem successor_new (v : s.Layer) (x : d.Space v.val) :
    (s.successor.vertex v.val v.property.le).toFun x = (s.batch.tile v).toFun x := by
  have fresh : ¬ d.depth v.val ≤ n := by rw [v.property]; omega
  dsimp only [successor]
  erw [dite_eq_right fresh]
  rfl

end Stage

noncomputable def stages : (n : Nat) → d.Stage n
  | 0 => d.initial
  | n + 1 => (stages n).successor

noncomputable def chain : IdealChain where
  Point n := (d.stages n).Point
  order n := (d.stages n).order
  next n := (d.stages n).batch.old

theorem vertex_coherent {n m : Nat} (hnm : n ≤ m) (v : V) (hv : d.depth v ≤ n) (x : d.Space v) :
    d.chain.up hnm ((d.stages n).vertex v hv |>.toFun x) =
      ((d.stages m).vertex v (Nat.le_trans hv hnm)).toFun x := by
  induction hnm with
  | refl => exact d.chain.up_self _ _
  | @step m h ih =>
    erw [d.chain.up_succ h, ih]
    exact ((d.stages m).successor_old v (le_trans hv h) x).symm

def Node := d.chain.Union
noncomputable def gluedOrder : MeetOrder d.Node := d.chain.unionOrder

noncomputable def vertex (v : V) : IdealEmbedding (d.order v) d.gluedOrder :=
  ((d.stages (d.depth v)).vertex v (le_refl _)).comp (d.chain.inclusion (d.depth v))

theorem vertex_at (v : V) (n : Nat) (hv : d.depth v ≤ n) (x : d.Space v) :
    (d.vertex v).toFun x = d.chain.point n (((d.stages n).vertex v hv).toFun x) := by
  change d.chain.point (d.depth v) (((d.stages (d.depth v)).vertex v (le_refl _)).toFun x) = _
  erw [← d.chain.include_up hv, d.vertex_coherent hv]

theorem vertex_principal (v : V) (top : d.Space v) (greatest : ∀ x, (d.order v).le x top)
    (z : d.Node) : d.gluedOrder.le z ((d.vertex v).toFun top) ↔ ∃ x, (d.vertex v).toFun x = z :=
  (d.vertex v).principal top greatest z

theorem vertex_greatest_part (v : V) (top : d.Space v) (greatest : ∀ x, (d.order v).le x top)
    (z : d.Node) (x : d.Space v) :
    d.gluedOrder.le ((d.vertex v).toFun x) z ↔
      (d.order v).le x ((d.vertex v).projection top z) :=
  (d.vertex v).greatest_part top greatest z x

end Scheme
end RootedGluing



namespace RootedGluing.Scheme

open Attachment
universe u
variable {V : Type u} (d : Scheme V)

theorem stage_cover (n : Nat) (x : (d.stages n).Point) :
    ∃ (v : V) (hv : d.depth v ≤ n) (a : d.Space v), ((d.stages n).vertex v hv).toFun a = x := by
  induction n with
  | zero => exact ⟨d.root, d.depth_root.le, x, rfl⟩
  | succ n ih =>
    rcases (d.stages n).batch.cover x with ⟨a, rfl⟩ | ⟨v, a, rfl⟩
    · rcases ih a with ⟨v, hv, b, eq⟩
      refine ⟨v, Nat.le_succ_of_le hv, b, ?_⟩
      exact ((d.stages n).successor_old v hv b).trans (congrArg _ eq)
    · exact ⟨v.val, v.property.le, a, (d.stages n).successor_new v a⟩

theorem cover (x : d.Node) : ∃ v a, (d.vertex v).toFun a = x := by
  rcases d.chain.cover x with ⟨n, a, rfl⟩
  rcases d.stage_cover n a with ⟨v, hv, b, eq⟩
  exact ⟨v, b, (d.vertex_at v n hv b).trans (congrArg _ eq)⟩

theorem comparison_in_vertex (x y : d.Node) (lower : d.gluedOrder.le x y) :
    ∃ v a b, (d.vertex v).toFun a = x ∧ (d.vertex v).toFun b = y ∧ (d.order v).le a b := by
  rcases d.cover y with ⟨v, b, rfl⟩
  rcases (d.vertex v).ideal b x lower with ⟨a, rfl⟩
  exact ⟨v, a, b, rfl, rfl, ((d.vertex v).le_iff _ _).mp lower⟩

theorem point_next (n : Nat) (x : (d.stages n).Point) :
    d.chain.point (n + 1) ((d.stages n).batch.old.toFun x) = d.chain.point n x := by
  have eq := d.chain.include_up (Nat.le_succ n) x
  erw [d.chain.up_succ (Nat.le_refl n), d.chain.up_self] at eq
  exact eq

theorem parent_identification (v : V) (h : d.depth v ≠ 0)
    (x : {x : d.Space v // (d.order v).le x (d.childAnchor v h)}) :
    (d.vertex v).toFun x.val = (d.vertex (d.parent v)).toFun ((d.link v h).toFun x).val := by
  let n := d.depth (d.parent v)
  let s := d.stages n
  let i : s.Layer := ⟨v, (d.parent_depth v h).symm⟩
  have base : (s.batch.tile i).toFun x.val =
      s.batch.old.toFun ((s.vertex (d.parent v) (s.parent_present i)).toFun ((d.link v h).toFun x).val) := by
    apply (s.batch.tile_old_overlap i x.val _).mpr
    exact ⟨x.property, rfl⟩
  exact (d.vertex_at v (n + 1) i.property.le x.val).trans
    ((congrArg (d.chain.point (n + 1)) (s.successor_new i x.val)).trans
      ((congrArg (d.chain.point (n + 1)) base).trans
        ((d.point_next n _).trans (d.vertex_at (d.parent v) n (s.parent_present i) _).symm)))

theorem fresh_old_meet (n : Nat) (x : (d.stages n).batch.Fresh) (a : (d.stages n).Point) :
    d.gluedOrder.meet (d.chain.point (n + 1) (.inr x)) (d.chain.point n a) =
      d.chain.point n ((d.stages n).order.meet
        (((d.stages n).batch.glue x.1).shadow x.2.val) a) := by
  rw [← d.point_next n a]
  change d.chain.unionOrder.meet
    ((d.chain.inclusion (n + 1)).toFun (.inr x))
    ((d.chain.inclusion (n + 1)).toFun ((d.stages n).batch.old.toFun a)) = _
  erw [← (d.chain.inclusion (n + 1)).map_meet]
  change d.chain.point (n + 1)
    ((d.stages n).batch.extension.meet (.inr x) ((d.stages n).batch.old.toFun a)) = _
  rw [(d.stages n).batch.fresh_old_meet, d.point_next]

theorem no_later_nodes_below_stage (n : Nat) (a : (d.stages n).Point) (x : d.Node)
    (lower : d.gluedOrder.le x (d.chain.point n a)) : ∃ b, d.chain.point n b = x :=
  (d.chain.inclusion n).ideal a x lower

end RootedGluing.Scheme



section

namespace EdgeWords
universe u
variable {E : Type u}

theorem append_reduced_or_cancelled (L : List (E × Bool)) (d : E × Bool)
    (h : NoBacktracking L) :
    NoBacktracking (L ++ [d]) ∨ ∃ pre, L = pre ++ [reverse d] := by
  classical
  induction L with
  | nil => exact Or.inl True.intro
  | cons a tail ih =>
    cases tail with
    | nil =>
      by_cases back : d = reverse a
      · refine Or.inr ⟨[], ?_⟩
        have twice : reverse (reverse a) = a := by
          rcases a with ⟨e, b⟩
          cases b <;> rfl
        rw [back, twice]
        rfl
      · exact Or.inl ⟨back, True.intro⟩
    | cons b tail =>
      rcases ih h.2 with reduced | ⟨pre, eq⟩
      · exact Or.inl ⟨h.1, reduced⟩
      · exact Or.inr ⟨a :: pre, congrArg (List.cons a) eq⟩

end EdgeWords

namespace CosetGeometry.TileStars
universe u
variable (J S R : Type u) [Group J] (request : S → R)

theorem depth_zero_iff (v : Vertex J S R) : depth J S R request v = 0 ↔ v = root J S R := by
  simp only [depth, List.length_eq_zero_iff, rootPath_empty_iff]

theorem edge_root_paths (d : Dart J S R) :
    rootPath J S R request (target J S R request d) =
      rootPath J S R request (source J S R request d) ++ [d] ∨
    rootPath J S R request (source J S R request d) =
      rootPath J S R request (target J S R request d) ++ [reverse J S R d] := by
  have first := rootPath_follows J S R request (source J S R request d)
  have reduced := rootPath_reduced J S R request (source J S R request d)
  rcases EdgeWords.append_reduced_or_cancelled _ d reduced with forward | ⟨pre, eq⟩
  · apply Or.inl
    exact rootPath_eq J S R request
      (follows_append J S R request first (Follows.cons d (Follows.nil _))) forward
  · rw [eq] at first reduced
    have prefixPath := (follows_last J S R request pre (reverse J S R d) first).1
    rw [source_reverse] at prefixPath
    have canonical := rootPath_eq J S R request prefixPath
      (EdgeWords.no_backtracking_append_left pre _ reduced)
    exact Or.inr (eq.trans (congrArg (fun L => L ++ [reverse J S R d]) canonical.symm))

noncomputable def incoming (v : Vertex J S R) (nonroot : v ≠ root J S R) : Dart J S R :=
  Classical.choose (exists_parent_edge J S R request v nonroot)

theorem incoming_target (v : Vertex J S R) (nonroot : v ≠ root J S R) :
    target J S R request (incoming J S R request v nonroot) = v :=
  (Classical.choose_spec (exists_parent_edge J S R request v nonroot)).1

theorem incoming_path (v : Vertex J S R) (nonroot : v ≠ root J S R) :
    rootPath J S R request v =
      rootPath J S R request (source J S R request (incoming J S R request v nonroot)) ++
        [incoming J S R request v nonroot] :=
  (Classical.choose_spec (exists_parent_edge J S R request v nonroot)).2.1

noncomputable def parent (v : Vertex J S R) : Vertex J S R := by
  classical
  exact if h : v = root J S R then root J S R else
    source J S R request (incoming J S R request v h)

theorem parent_eq (v : Vertex J S R) (nonroot : v ≠ root J S R) :
    parent J S R request v = source J S R request (incoming J S R request v nonroot) := by
  simp only [parent, dite_eq_right nonroot]

theorem parent_depth (v : Vertex J S R) (nonzero : depth J S R request v ≠ 0) :
    depth J S R request (parent J S R request v) + 1 = depth J S R request v := by
  have nonroot : v ≠ root J S R := fun h => nonzero ((depth_zero_iff J S R request v).mpr h)
  rw [parent_eq J S R request v nonroot]
  exact (Classical.choose_spec (exists_parent_edge J S R request v nonroot)).2.2.symm

theorem extension_nonroot (d : Dart J S R)
    (eq : rootPath J S R request (target J S R request d) =
      rootPath J S R request (source J S R request d) ++ [d]) :
    target J S R request d ≠ root J S R := by
  intro h
  rw [h, rootPath_root] at eq
  have lengths := congrArg List.length eq
  simp only [List.length_nil, List.length_append, List.length_cons] at lengths
  omega

theorem incoming_of_extension (d : Dart J S R)
    (eq : rootPath J S R request (target J S R request d) =
      rootPath J S R request (source J S R request d) ++ [d]) :
    incoming J S R request (target J S R request d)
      (extension_nonroot J S R request d eq) = d := by
  have other := incoming_path J S R request (target J S R request d)
    (extension_nonroot J S R request d eq)
  have lasts := congrArg List.getLast? (other.symm.trans eq)
  simpa only [List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.some.injEq] using lasts

theorem edge_is_parent (d : Dart J S R) :
    (target J S R request d ≠ root J S R ∧
      parent J S R request (target J S R request d) = source J S R request d) ∨
    (source J S R request d ≠ root J S R ∧
      parent J S R request (source J S R request d) = target J S R request d) := by
  rcases edge_root_paths J S R request d with forward | backward
  · have nonroot := extension_nonroot J S R request d forward
    exact Or.inl ⟨nonroot, (parent_eq J S R request _ nonroot).trans
      (congrArg (source J S R request) (incoming_of_extension J S R request d forward))⟩
  · have reversed : rootPath J S R request (target J S R request (reverse J S R d)) =
        rootPath J S R request (source J S R request (reverse J S R d)) ++ [reverse J S R d] := by
      rw [source_reverse, target_reverse]
      exact backward
    have nonroot := extension_nonroot J S R request (reverse J S R d) reversed
    have same := (parent_eq J S R request _ nonroot).trans
      (congrArg (source J S R request) (incoming_of_extension J S R request (reverse J S R d) reversed))
    simp only [source_reverse, target_reverse] at nonroot same
    exact Or.inr ⟨nonroot, same⟩

end CosetGeometry.TileStars
end



namespace CosetGeometry.TileStars
universe u
variable (J S R : Type u) [Group J] (request : S → R)

theorem parent_root : parent J S R request (root J S R) = root J S R := by
  simp [parent]

theorem parent_of_depth_edge (d : Dart J S R)
    (lower : depth J S R request (source J S R request d) + 1 = depth J S R request (target J S R request d)) :
    parent J S R request (target J S R request d) = source J S R request d := by
  rcases edge_is_parent J S R request d with ⟨_, forward⟩ | ⟨nonroot, backward⟩
  · exact forward
  · have nonzero : depth J S R request (source J S R request d) ≠ 0 :=
      fun zero => nonroot ((depth_zero_iff J S R request _).1 zero)
    have bound := parent_depth J S R request _ nonzero
    rw [backward] at bound
    omega

theorem parent_iff (v p : Vertex J S R) :
    parent J S R request v = p ↔ (v = root J S R ∧ p = root J S R) ∨
      ((∃ d : Dart J S R, source J S R request d = p ∧ target J S R request d = v) ∧
        depth J S R request p + 1 = depth J S R request v) := by
  constructor
  · rintro rfl
    by_cases equal : v = root J S R
    · exact Or.inl ⟨equal, equal ▸ parent_root J S R request⟩
    · exact Or.inr ⟨⟨incoming J S R request v equal, (parent_eq J S R request v equal).symm,
        incoming_target J S R request v equal⟩,
        parent_depth J S R request v (fun zero => equal ((depth_zero_iff J S R request v).1 zero))⟩
  · rintro (⟨rfl, rfl⟩ | ⟨⟨d, src, tgt⟩, lower⟩)
    · exact parent_root J S R request
    · rw [← src, ← tgt] at lower ⊢
      exact parent_of_depth_edge J S R request d lower

theorem incoming_iff (v : Vertex J S R) (nonroot : v ≠ root J S R) (d : Dart J S R) :
    incoming J S R request v nonroot = d ↔ target J S R request d = v ∧
      depth J S R request (source J S R request d) + 1 = depth J S R request v := by
  constructor
  · rintro rfl
    refine ⟨incoming_target J S R request v nonroot, ?_⟩
    rw [← parent_eq J S R request v nonroot]
    exact parent_depth J S R request v (fun zero => nonroot ((depth_zero_iff J S R request v).1 zero))
  · rintro ⟨tgt, lower⟩
    have lower' := lower
    rw [← tgt] at lower'
    rcases edge_root_paths J S R request d with forward | backward
    · have same := incoming_of_extension J S R request d forward
      simpa only [tgt] using same
    · have lengths := congrArg List.length backward
      change depth J S R request (source J S R request d) =
        (rootPath J S R request (target J S R request d) ++ [reverse J S R d]).length at lengths
      rw [List.length_append, List.length_singleton] at lengths
      change depth J S R request (source J S R request d) = depth J S R request (target J S R request d) + 1 at lengths
      omega

end CosetGeometry.TileStars



namespace CosetGeometry.TileStars

open Attachment
universe u
variable (J S R : Type u) [Group J] (request : S → R)

structure Spaces where
  Space : Vertex J S R → Type u
  order : ∀ v, MeetOrder (Space v)
  leftAnchor : ∀ e : Edge J S R, Space (source J S R request (e, true))
  rightAnchor : ∀ e : Edge J S R, Space (target J S R request (e, true))
  overlap : ∀ e, MeetIso
    (idealOrder (order (source J S R request (e, true))) (leftAnchor e))
    (idealOrder (order (target J S R request (e, true))) (rightAnchor e))

namespace Spaces
variable {J S R request} (g : Spaces J S R request)

def anchor (d : Dart J S R) : g.Space (source J S R request d) := by
  rcases d with ⟨e, b⟩
  cases b
  · exact g.rightAnchor e
  · exact g.leftAnchor e

def arrow (d : Dart J S R) : MeetIso
    (idealOrder (g.order (source J S R request d)) (g.anchor d))
    (idealOrder (g.order (target J S R request d)) (g.anchor (reverse J S R d))) := by
  rcases d with ⟨e, b⟩
  cases b
  · exact inverseIso (g.overlap e)
  · exact g.overlap e

def edgeInput (d : Dart J S R) : PrincipalAmalgamation.Input
    (g.order (source J S R request d)) (g.order (target J S R request d)) where
  leftAnchor := g.anchor d
  rightAnchor := g.anchor (reverse J S R d)
  overlap := inverseIso (g.arrow d)

def reindexInput {v w v' w' : Vertex J S R} (hv : v = v') (hw : w = w')
    (i : PrincipalAmalgamation.Input (g.order v) (g.order w)) :
    PrincipalAmalgamation.Input (g.order v') (g.order w') := hv ▸ hw ▸ i

noncomputable def localGlue (v : Vertex J S R) (nonzero : depth J S R request v ≠ 0) :
    PrincipalAmalgamation.Input (g.order (parent J S R request v)) (g.order v) := by
  have nonroot : v ≠ root J S R := fun h => nonzero ((depth_zero_iff J S R request v).mpr h)
  exact g.reindexInput (parent_eq J S R request v nonroot).symm
    (incoming_target J S R request v nonroot) (g.edgeInput (incoming J S R request v nonroot))

noncomputable def scheme : RootedGluing.Scheme (Vertex J S R) where
  root := root J S R
  depth := depth J S R request
  depth_root := (depth_zero_iff J S R request _).mpr rfl
  zero_eq_root v := (depth_zero_iff J S R request v).mp
  parent := parent J S R request
  parent_depth := parent_depth J S R request
  Space := g.Space
  order := g.order
  childAnchor v h := (g.localGlue v h).rightAnchor
  parentAnchor v h := (g.localGlue v h).leftAnchor
  link v h := (g.localGlue v h).overlap

def Node := g.scheme.Node
noncomputable def gluedOrder : MeetOrder g.Node := g.scheme.gluedOrder
noncomputable def vertex (v : Vertex J S R) : IdealEmbedding (g.order v) g.gluedOrder :=
  g.scheme.vertex v

theorem vertex_principal (v : Vertex J S R) (top : g.Space v)
    (greatest : ∀ x, (g.order v).le x top) (z : g.Node) :
    g.gluedOrder.le z ((g.vertex v).toFun top) ↔ ∃ x, (g.vertex v).toFun x = z :=
  g.scheme.vertex_principal v top greatest z

theorem vertex_greatest_part (v : Vertex J S R) (top : g.Space v)
    (greatest : ∀ x, (g.order v).le x top) (z : g.Node) (x : g.Space v) :
    g.gluedOrder.le ((g.vertex v).toFun x) z ↔
      (g.order v).le x ((g.vertex v).projection top z) :=
  g.scheme.vertex_greatest_part v top greatest z x

theorem parent_identification (v : Vertex J S R) (h : depth J S R request v ≠ 0)
    (x : {x : g.Space v // (g.order v).le x (g.localGlue v h).rightAnchor}) :
    (g.vertex v).toFun x.val =
      (g.vertex (parent J S R request v)).toFun ((g.localGlue v h).overlap.toFun x).val :=
  g.scheme.parent_identification v h x

theorem cover (z : g.Node) : ∃ v x, (g.vertex v).toFun x = z := g.scheme.cover z

theorem comparison_in_vertex (x y : g.Node) (lower : g.gluedOrder.le x y) :
    ∃ v a b, (g.vertex v).toFun a = x ∧ (g.vertex v).toFun b = y ∧ (g.order v).le a b :=
  g.scheme.comparison_in_vertex x y lower

end Spaces
end CosetGeometry.TileStars

end PartitionPilot.Compression.RecursiveMaps

end OAI
