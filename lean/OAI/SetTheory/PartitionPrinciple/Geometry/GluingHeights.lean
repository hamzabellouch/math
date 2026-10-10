import OAI.SetTheory.PartitionPrinciple.Definability.NatUnionCodes
import OAI.SetTheory.PartitionPrinciple.Models.RootedGluingQuotient

namespace OAI


namespace PartitionPilot

namespace Compression.RecursiveMaps.CosetGeometry

universe u
variable (J S : Type u) [Group J]

theorem representative_exists (v : Vertex J S) : ∃ w, point J S w = v := by
  induction v using Quotient.ind with
  | _ w => exact ⟨w, rfl⟩

noncomputable def representative (v : Vertex J S) : External J S := by
  classical
  exact if v = root J S then 1 else Classical.choose (representative_exists J S v)

theorem representative_spec (v : Vertex J S) : point J S (representative J S v) = v := by
  classical
  by_cases h : v = root J S
  · subst v
    simp only [representative]
    rfl
  · simp only [representative, ite_eq_right h]
    exact Classical.choose_spec (representative_exists J S v)

theorem representative_root : representative J S (root J S) = 1 := by
  simp [representative]

theorem coordinate_exists (w : External J S) :
    ∃ j, representative J S (point J S w) * old J S j = w :=
  (point_eq J S _ w).mp (representative_spec J S (point J S w))

noncomputable def coordinate (w : External J S) : J := Classical.choose (coordinate_exists J S w)

theorem coordinate_spec (w : External J S) :
    representative J S (point J S w) * old J S (coordinate J S w) = w :=
  Classical.choose_spec (coordinate_exists J S w)

theorem coordinate_unique (w : External J S) (j : J)
    (eq : representative J S (point J S w) * old J S j = w) : coordinate J S w = j :=
  old_injective J S (mul_left_cancel ((coordinate_spec J S w).trans eq.symm))

theorem point_mul_old (w : External J S) (j : J) : point J S (w * old J S j) = point J S w :=
  ((point_eq J S w (w * old J S j)).mpr ⟨j, rfl⟩).symm

theorem coordinate_mul_old (w : External J S) (j : J) :
    coordinate J S (w * old J S j) = coordinate J S w * j := by
  apply coordinate_unique J S
  rw [point_mul_old, map_mul, ← mul_assoc, coordinate_spec]

theorem coordinate_one : coordinate J S 1 = 1 := by
  apply coordinate_unique J S
  change representative J S (root J S) * old J S 1 = 1
  rw [representative_root, map_one, mul_one]

theorem coordinate_old (j : J) : coordinate J S (old J S j) = j := by
  have h := coordinate_mul_old J S 1 j
  simpa only [one_mul, coordinate_one] using h

structure OrderAction {A : Type u} (P : MeetOrder A) where
  iso : J → MeetIso P P
  one : ∀ x, (iso 1).toFun x = x
  mul : ∀ g h x, (iso (g * h)).toFun x = (iso g).toFun ((iso h).toFun x)

namespace OrderAction
variable {J S} {A : Type u} {P : MeetOrder A} (a : OrderAction J P)

noncomputable def chart (w : External J S) : MeetIso P P := a.iso (coordinate J S w)

theorem chart_one (x : A) : (a.chart (S := S) 1).toFun x = x := by
  change (a.iso (coordinate J S 1)).toFun x = x
  rw [coordinate_one, a.one]

theorem chart_mul_old (w : External J S) (j : J) (x : A) :
    (a.chart (w * old J S j)).toFun x = (a.chart w).toFun ((a.iso j).toFun x) := by
  change (a.iso (coordinate J S (w * old J S j))).toFun x = _
  rw [coordinate_mul_old, a.mul]
  rfl

def Label (_a : OrderAction J P) := Vertex J S × A

noncomputable def label (w : External J S) (x : A) : a.Label (S := S) :=
  (point J S w, (a.chart w).toFun x)

theorem label_mul_old (w : External J S) (j : J) (x : A) :
    a.label (w * old J S j) x = a.label w ((a.iso j).toFun x) := by
  apply Prod.ext
  · exact point_mul_old J S w j
  · exact a.chart_mul_old w j x

theorem label_same_rep (w : External J S) (x y : A) : a.label w x = a.label w y ↔ x = y := by
  constructor
  · intro eq
    exact embedding_injective (a.chart w).toMeetEmbedding (congrArg Prod.snd eq)
  · rintro rfl
    rfl

theorem label_eq_iff (w v : External J S) (x y : A) :
    a.label w x = a.label v y ↔ ∃ j, w * old J S j = v ∧ x = (a.iso j).toFun y := by
  constructor
  · intro eq
    have cosets := congrArg Prod.fst eq
    rcases (point_eq J S w v).mp cosets with ⟨j, rfl⟩
    rw [a.label_mul_old] at eq
    exact ⟨j, rfl, (a.label_same_rep _ _ _).mp eq⟩
  · rintro ⟨j, rfl, rfl⟩
    exact (a.label_mul_old w j y).symm

def ideal (j : J) : IdealEmbedding P P where
  toMeetEmbedding := (a.iso j).toMeetEmbedding
  ideal _ x _ := ⟨(a.iso j).inverse x, (a.iso j).right_inverse x⟩

theorem fixes_top (T : A) (greatest : ∀ x, P.le x T) (j : J) : (a.iso j).toFun T = T := by
  apply P.antisymm (greatest _)
  have lower := ((a.iso j).le_iff _ _).mpr (greatest ((a.iso j).inverse T))
  rw [(a.iso j).right_inverse] at lower
  exact lower

end OrderAction

def taskSystem_orderAction {A G Task Label : Type u} {P : MeetOrder A}
    (f : TaskSystem P G Task Label) :
    letI : Group G := groupOfData f.group
    OrderAction G P := by
  letI : Group G := groupOfData f.group
  exact { iso := f.action, one := f.action_one, mul := f.action_mul }

end Compression.RecursiveMaps.CosetGeometry



namespace SetRealization

open Compression.RecursiveMaps.CosetGeometry
universe u

structure GeometryPresentation (A G : Type u) where
  points : Presentation A
  actors : Presentation G

namespace GeometryPresentation

variable {A G : Type u} [Group G] (s : GeometryPresentation A G)

noncomputable def orderRelation (P : MeetOrder A) : ZFSet.{u} :=
  (s.points.product s.points).subset (fun xy => P.le xy.1 xy.2)

noncomputable def meetGraph (P : MeetOrder A) : ZFSet.{u} :=
  (s.points.product s.points).graph s.points (fun xy => P.meet xy.1 xy.2)

noncomputable def multiplicationGraph : ZFSet.{u} :=
  (s.actors.product s.actors).graph s.actors (fun gh => gh.1 * gh.2)

noncomputable def inverseGraph : ZFSet.{u} :=
  s.actors.graph s.actors (fun g => g⁻¹)

noncomputable def actionGraph (P : MeetOrder A) (a : OrderAction G P) : ZFSet.{u} :=
  (s.actors.product s.points).graph s.points (fun gx => (a.iso gx.1).toFun gx.2)

noncomputable def package (P : MeetOrder A) (a : OrderAction G P) (bottom : A) : ZFSet.{u} :=
  ZFSet.pair s.points.carrier (ZFSet.pair s.actors.carrier
    (ZFSet.pair (s.orderRelation P) (ZFSet.pair (s.meetGraph P)
      (ZFSet.pair s.multiplicationGraph (ZFSet.pair s.inverseGraph
        (ZFSet.pair (s.actionGraph P a) (ZFSet.pair (s.points.encode bottom) (s.actors.encode 1))))))))

omit [Group G] in
theorem orderRelation_iff (P : MeetOrder A) (x y : A) :
    ZFSet.pair (s.points.encode x) (s.points.encode y) ∈ s.orderRelation P ↔ P.le x y :=
  (s.points.product s.points).encode_mem_subset (fun xy => P.le xy.1 xy.2) (x, y)

omit [Group G] in
theorem meetGraph_iff (P : MeetOrder A) (x y z : A) :
    ZFSet.pair (ZFSet.pair (s.points.encode x) (s.points.encode y)) (s.points.encode z)
      ∈ s.meetGraph P ↔ P.meet x y = z :=
  (s.points.product s.points).pair_mem_graph s.points _ (x, y) z

theorem multiplicationGraph_iff (g h k : G) :
    ZFSet.pair (ZFSet.pair (s.actors.encode g) (s.actors.encode h)) (s.actors.encode k)
      ∈ s.multiplicationGraph ↔ g * h = k :=
  (s.actors.product s.actors).pair_mem_graph s.actors _ (g, h) k

theorem inverseGraph_iff (g h : G) :
    ZFSet.pair (s.actors.encode g) (s.actors.encode h) ∈ s.inverseGraph ↔ g⁻¹ = h :=
  s.actors.pair_mem_graph s.actors _ g h

theorem actionGraph_iff (P : MeetOrder A) (a : OrderAction G P) (g : G) (x y : A) :
    ZFSet.pair (ZFSet.pair (s.actors.encode g) (s.points.encode x)) (s.points.encode y)
      ∈ s.actionGraph P a ↔ (a.iso g).toFun x = y :=
  (s.actors.product s.points).pair_mem_graph s.points _ (g, x) y

theorem operation_graphs_are_functions (P : MeetOrder A) (a : OrderAction G P) :
    ZFSet.IsFunc (ZFSet.prod s.points.carrier s.points.carrier) s.points.carrier (s.meetGraph P) ∧
    ZFSet.IsFunc (ZFSet.prod s.actors.carrier s.actors.carrier) s.actors.carrier s.multiplicationGraph ∧
    ZFSet.IsFunc s.actors.carrier s.actors.carrier s.inverseGraph ∧
    ZFSet.IsFunc (ZFSet.prod s.actors.carrier s.points.carrier) s.points.carrier (s.actionGraph P a) :=
  ⟨(s.points.product s.points).graph_isFunc s.points _,
    (s.actors.product s.actors).graph_isFunc s.actors _,
    s.actors.graph_isFunc s.actors _,
    (s.actors.product s.points).graph_isFunc s.points _⟩

structure RankBounds (P : MeetOrder A) (a : OrderAction G P) (bottom : A) (o : Ordinal.{u}) : Prop where
  points : ZFSet.rank s.points.carrier < o
  actors : ZFSet.rank s.actors.carrier < o
  order_relation : ZFSet.rank (s.orderRelation P) < o
  meet_graph : ZFSet.rank (s.meetGraph P) < o
  multiplication_graph : ZFSet.rank s.multiplicationGraph < o
  inverse_graph : ZFSet.rank s.inverseGraph < o
  action_graph : ZFSet.rank (s.actionGraph P a) < o
  bottom_code : ZFSet.rank (s.points.encode bottom) < o
  identity_code : ZFSet.rank (s.actors.encode 1) < o
  package : ZFSet.rank (s.package P a bottom) < o

theorem rank_bounds (P : MeetOrder A) (a : OrderAction G P) (bottom : A)
    {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (hp : ZFSet.rank s.points.carrier < o) (hg : ZFSet.rank s.actors.carrier < o) :
    s.RankBounds P a bottom o := by
  have pp := s.points.product_rank_lt limit s.points hp hp
  have gg := s.actors.product_rank_lt limit s.actors hg hg
  have gp := s.actors.product_rank_lt limit s.points hg hp
  have orderBound : ZFSet.rank (s.orderRelation P) < o :=
    (s.points.product s.points).subset_rank_lt pp _
  have meetBound : ZFSet.rank (s.meetGraph P) < o :=
    (s.points.product s.points).graph_rank_lt s.points _ limit pp hp
  have mulBound : ZFSet.rank s.multiplicationGraph < o :=
    (s.actors.product s.actors).graph_rank_lt s.actors _ limit gg hg
  have invBound : ZFSet.rank s.inverseGraph < o :=
    s.actors.graph_rank_lt s.actors _ limit hg hg
  have actionBound : ZFSet.rank (s.actionGraph P a) < o :=
    (s.actors.product s.points).graph_rank_lt s.points _ limit gp hp
  have bottomBound : ZFSet.rank (s.points.encode bottom) < o :=
    (ZFSet.rank_lt_of_mem (s.points.encode_mem bottom)).trans hp
  have oneBound : ZFSet.rank (s.actors.encode 1) < o :=
    (ZFSet.rank_lt_of_mem (s.actors.encode_mem 1)).trans hg
  refine ⟨hp, hg, orderBound, meetBound, mulBound, invBound, actionBound, bottomBound, oneBound, ?_⟩
  exact rank_orderedPair_lt limit hp (rank_orderedPair_lt limit hg
    (rank_orderedPair_lt limit orderBound (rank_orderedPair_lt limit meetBound
      (rank_orderedPair_lt limit mulBound (rank_orderedPair_lt limit invBound
        (rank_orderedPair_lt limit actionBound (rank_orderedPair_lt limit bottomBound oneBound)))))))

end GeometryPresentation
end SetRealization



namespace Compression.RecursiveMaps.TileRequests

open Attachment
universe u
variable {A : Type u} (P : MeetOrder A)

structure Tile (Child : Type u) where
  Space : Type u
  order : MeetOrder Space
  root : IdealEmbedding P order
  child : Child → IdealEmbedding P order
  cover : ∀ z, (∃ x, root.toFun x = z) ∨ ∃ j x, (child j).toFun x = z

namespace Tile
variable {P}

noncomputable def binary (g : PrincipalAmalgamation.Input P P) : Tile P (ULift.{u} Unit) where
  Space := g.Node
  order := g.order
  root := { toMeetEmbedding := g.left, ideal := g.left_ideal }
  child _ := { toMeetEmbedding := g.right, ideal := g.right_ideal }
  cover z := by
    rcases g.cover z with ⟨x, eq⟩ | ⟨x, eq⟩
    · exact Or.inl ⟨x, eq⟩
    · exact Or.inr ⟨⟨()⟩, x, eq⟩

noncomputable def rectangle (r : Rectangle.Input P) : Tile P (ULift.{u} Bool) where
  Space := r.copies.Node
  order := r.copies.order
  root := { toMeetEmbedding := r.root, ideal := r.copies.vertex_ideal .root }
  child j := match j.down with
    | false => { toMeetEmbedding := r.first, ideal := r.copies.vertex_ideal .one }
    | true => { toMeetEmbedding := r.second, ideal := r.copies.vertex_ideal .two }
  cover z := by
    rcases r.three_vertex_cover z with ⟨i, x, eq⟩
    cases i with
    | root => exact Or.inl ⟨x, eq⟩
    | one => exact Or.inr ⟨⟨false⟩, x, eq⟩
    | two => exact Or.inr ⟨⟨true⟩, x, eq⟩

end Tile

inductive Request where
  | separation (W : A)
  | compression (K : A) (copy : MeetIso P (idealOrder P K))
  | rectangle (data : Rectangle.Input P)

namespace Request
variable {P}

def Child : Request P → Type u
  | .separation _ => ULift.{u} Unit
  | .compression _ _ => ULift.{u} Unit
  | .rectangle _ => ULift.{u} Bool

noncomputable def tile (T : A) (greatest : ∀ x, P.le x T) : (r : Request P) → Tile P r.Child
  | .separation W => Tile.binary (BinaryTiles.separation P W)
  | .compression K copy => Tile.binary (BinaryTiles.compression P T K greatest copy)
  | .rectangle r => Tile.rectangle r

theorem separation_agrees (T : A) (greatest : ∀ x, P.le x T) (W x : A) (below : P.le x W) :
    (((Request.separation W).tile T greatest).child ⟨()⟩).toFun x =
      ((Request.separation W).tile T greatest).root.toFun x :=
  BinaryTiles.separation_fixes P W x below

theorem compression_agrees (T : A) (greatest : ∀ x, P.le x T) (K : A)
    (copy : MeetIso P (idealOrder P K)) (x : A) :
    (((Request.compression K copy).tile T greatest).child ⟨()⟩).toFun x =
      ((Request.compression K copy).tile T greatest).root.toFun (copy.toFun x).val :=
  BinaryTiles.compression_identification P T K greatest copy x

theorem rectangle_agrees (T : A) (greatest : ∀ x, P.le x T) (r : Rectangle.Input P) (x : A)
    (below : P.le x r.C) :
    (((Request.rectangle r).tile T greatest).child ⟨false⟩).toFun x =
      ((Request.rectangle r).tile T greatest).root.toFun (r.g1.toFun x) ∧
    (((Request.rectangle r).tile T greatest).child ⟨true⟩).toFun x =
      ((Request.rectangle r).tile T greatest).root.toFun (r.g2.toFun x) :=
  ⟨r.first_agrees x below, r.second_agrees x below⟩

end Request

structure Family (R : Type u) where
  top : A
  greatest : ∀ x, P.le x top
  request : R → Request P

namespace Family
variable {P} {R : Type u} (f : Family P R)

def Child (r : R) := (f.request r).Child
def Letters := Sigma f.Child
noncomputable def tile (r : R) : Tile P (f.Child r) := (f.request r).tile f.top f.greatest

noncomputable def all (T : A) (greatest : ∀ x, P.le x T) : Family P (Request P) :=
  ⟨T, greatest, id⟩

end Family

end Compression.RecursiveMaps.TileRequests



namespace Compression.RecursiveMaps.CosetGeometry.TileStars.Spaces

open Attachment
universe u
variable {J S R : Type u} [Group J] {request : S → R} (g : Spaces J S R request)
variable {B : Type u} (value : ∀ v, g.Space v → B)

def Realizes (v w : Vertex J S R) (i : PrincipalAmalgamation.Input (g.order v) (g.order w)) : Prop :=
  ∀ x : {x : g.Space w // (g.order w).le x i.rightAnchor},
    value w x.val = value v (i.overlap.toFun x).val

theorem realizes_reindex {v w v' w' : Vertex J S R} (hv : v = v') (hw : w = w')
    (i : PrincipalAmalgamation.Input (g.order v) (g.order w)) :
    g.Realizes value v' w' (g.reindexInput hv hw i) ↔ g.Realizes value v w i := by
  cases hv
  cases hw
  rfl

def Equation (d : Dart J S R) : Prop :=
  ∀ x : {x : g.Space (source J S R request d) //
      (g.order (source J S R request d)).le x (g.anchor d)},
    value (source J S R request d) x.val =
      value (target J S R request d) ((g.arrow d).toFun x).val

theorem equation_of_reverse (d : Dart J S R) (h : g.Equation value (reverse J S R d)) :
    g.Equation value d := by
  rcases d with ⟨e, b⟩
  cases b
  · intro y
    have eq := h ((g.overlap e).inverse y)
    change value (source J S R request (e, true)) ((g.overlap e).inverse y).val =
      value (target J S R request (e, true)) ((g.overlap e).toFun ((g.overlap e).inverse y)).val at eq
    erw [(g.overlap e).right_inverse] at eq
    exact eq.symm
  · intro x
    have eq := h ((g.overlap e).toFun x)
    change value (target J S R request (e, true)) ((g.overlap e).toFun x).val =
      value (source J S R request (e, true)) ((g.overlap e).inverse ((g.overlap e).toFun x)).val at eq
    erw [(g.overlap e).left_inverse] at eq
    exact eq.symm

section
variable (parents : ∀ v (h : depth J S R request v ≠ 0),
  g.Realizes value (parent J S R request v) v (g.localGlue v h))
include parents

theorem incoming_realizes (v : Vertex J S R) (nonroot : v ≠ root J S R) :
    g.Realizes value (source J S R request (incoming J S R request v nonroot))
      (target J S R request (incoming J S R request v nonroot))
      (g.edgeInput (incoming J S R request v nonroot)) := by
  have nonzero : depth J S R request v ≠ 0 := fun h => nonroot ((depth_zero_iff J S R request v).mp h)
  exact (g.realizes_reindex value (parent_eq J S R request v nonroot).symm
    (incoming_target J S R request v nonroot) _).mp (parents v nonzero)

theorem equation_of_extension (d : Dart J S R)
    (eq : rootPath J S R request (target J S R request d) =
      rootPath J S R request (source J S R request d) ++ [d]) : g.Equation value d := by
  have realized := g.incoming_realizes value parents (target J S R request d)
    (extension_nonroot J S R request d eq)
  rw [incoming_of_extension J S R request d eq] at realized
  intro x
  have same := realized ((g.arrow d).toFun x)
  change value (target J S R request d) ((g.arrow d).toFun x).val =
    value (source J S R request d) ((g.arrow d).inverse ((g.arrow d).toFun x)).val at same
  rw [(g.arrow d).left_inverse] at same
  exact same.symm

theorem equations_of_parents (d : Dart J S R) : g.Equation value d := by
  rcases edge_root_paths J S R request d with forward | backward
  · exact g.equation_of_extension value parents d forward
  · apply g.equation_of_reverse value d
    apply g.equation_of_extension value parents (reverse J S R d)
    simpa only [source_reverse, target_reverse] using backward

end

theorem edge_identification (d : Dart J S R)
    (x : {x : g.Space (source J S R request d) //
      (g.order (source J S R request d)).le x (g.anchor d)}) :
    (g.vertex (source J S R request d)).toFun x.val =
      (g.vertex (target J S R request d)).toFun ((g.arrow d).toFun x).val :=
  g.equations_of_parents (fun v => (g.vertex v).toFun)
    (fun v h => g.parent_identification v h) d x

end Compression.RecursiveMaps.CosetGeometry.TileStars.Spaces



namespace Compression.RecursiveMaps

open RationalHeights
universe u v w

namespace IdealEmbedding
variable {A : Type u} {B : Type v} {H : Type w}
    {P : MeetOrder A} {Q : MeetOrder B}

theorem projection_mono (f : IdealEmbedding P Q) (top : A) {x y : B}
    (lower : Q.le x y) : P.le (f.projection top x) (f.projection top y) := by
  apply (f.le_iff _ _).mp
  rw [f.projection_spec, f.projection_spec]
  exact Q.le_meet (Q.trans (Q.meet_le_left _ _) lower) (Q.meet_le_right _ _)

theorem projection_image (f : IdealEmbedding P Q) (top : A)
    (greatest : ∀ a, P.le a top) (a : A) : f.projection top (f.toFun a) = a := by
  apply embedding_injective f.toMeetEmbedding
  rw [f.projection_spec]
  exact Q.antisymm (Q.meet_le_left _ _)
    (Q.le_meet (Q.refl _) ((f.le_iff _ _).mpr (greatest a)))

theorem projected_strict (f : IdealEmbedding P Q) (top : A)
    (greatest : ∀ a, P.le a top) {R : HeightOrder H} (height : StrictHeight P R)
    (x y : B) (lower : Q.le x y) (different : x ≠ y) (in_copy : ∃ a, f.toFun a = y) :
    R.lt (height.value (f.projection top x)) (height.value (f.projection top y)) := by
  rcases in_copy with ⟨b, rfl⟩
  rcases f.ideal b x lower with ⟨a, rfl⟩
  rw [f.projection_image top greatest, f.projection_image top greatest]
  exact height.strict a b ((f.le_iff _ _).mp lower)
    (fun eq => different (congrArg f.toFun eq))

end IdealEmbedding

namespace LinearHeightOrder
variable {H : Type u} {K : Type v}

theorem lex_weak (R : LinearHeightOrder H) (S : LinearHeightOrder K) {x y : H × K}
    (first : R.Weak x.1 y.1) (second : S.Weak x.2 y.2) : (R.lex S).Weak x y := by
  rcases first with eq | lower
  · rcases second with eq' | lower
    · exact Or.inl (Prod.ext eq eq')
    · exact Or.inr (Or.inr ⟨eq, lower⟩)
  · exact Or.inr (Or.inl lower)

theorem lex_strict (R : LinearHeightOrder H) (S : LinearHeightOrder K) {x y : H × K}
    (first : R.Weak x.1 y.1)
    (strict : R.lt x.1 y.1 ∨ S.lt x.2 y.2) : (R.lex S).lt x y := by
  rcases first with eq | lower
  · rcases strict with lower | lower
    · exact False.elim (R.irrefl _ (eq ▸ lower))
    · exact Or.inr ⟨eq, lower⟩
  · exact Or.inl lower

end LinearHeightOrder

theorem countable_range_pair {X : Type u} {H : Type v} {K : Type w}
    {f : X → H} {g : X → K} (hf : CountableRange f) (hg : CountableRange g) :
    CountableRange (fun x => (f x, g x)) := by
  rcases hf with ⟨a, ha⟩
  rcases hg with ⟨b, hb⟩
  exact ⟨fun x => natPair (a x) (b x), fun x y eq =>
    Prod.ext (ha x y (natPair_injective eq).1) (hb x y (natPair_injective eq).2)⟩

theorem countable_range_precompose {X : Type u} {Y : Type v} {H : Type w}
    {f : Y → H} (hf : CountableRange f) (g : X → Y) : CountableRange (fun x => f (g x)) := by
  rcases hf with ⟨code, equal⟩
  exact ⟨fun x => code (g x), fun x y eq => equal (g x) (g y) eq⟩

namespace RationalHeights

def zero : Rational := Rational.mk ⟨0, 1, by decide⟩
def one : Rational := Rational.mk ⟨1, 1, by decide⟩

theorem zero_lt_one : Rational.lt zero one := by
  change (0 : Int) * 1 < 1 * 1
  decide

theorem rational_assignment {X : Type u} {H : Type v} {P : MeetOrder X}
    (R : LinearHeightOrder H) (seed : StrictHeight P R.toHeightOrder)
    (base : X) (countable : CountableRange seed.value) :
    ∃ height : StrictHeight P Rational.order.toHeightOrder,
      ∀ x, Rational.lt zero (height.value x) ∧ Rational.lt (height.value x) one := by
  rcases countable_range_interpolation R Rational.order seed.value base countable
    zero one zero_lt_one with ⟨assign, bounds, strict, _⟩
  exact ⟨⟨assign, fun x y lower different => strict x y (seed.strict x y lower different)⟩, bounds⟩

end RationalHeights

namespace TileRequests.Tile
variable {A : Type u} {H : Type v} {P : MeetOrder A}
    (top : A) (greatest : ∀ a, P.le a top)
    (R : LinearHeightOrder H) (seed : StrictHeight P R.toHeightOrder)

noncomputable def binaryTuple (t : Tile P (ULift.{u} Unit)) :
    StrictHeight t.order (R.lex R).toHeightOrder where
  value x := (seed.value (t.root.projection top x),
    seed.value ((t.child ⟨()⟩).projection top x))
  strict x y lower different := by
    apply R.lex_strict R (seed.mono (t.root.projection_mono top lower))
    rcases t.cover y with root | ⟨j, a, eq⟩
    · exact Or.inl (t.root.projected_strict top greatest seed x y lower different root)
    · rcases j with ⟨⟨⟩⟩
      exact Or.inr ((t.child ⟨()⟩).projected_strict top greatest seed x y lower different ⟨a, eq⟩)

noncomputable def rectangleTuple (t : Tile P (ULift.{u} Bool)) :
    StrictHeight t.order (R.lex (R.lex R)).toHeightOrder where
  value x := (seed.value (t.root.projection top x),
    seed.value ((t.child ⟨false⟩).projection top x),
    seed.value ((t.child ⟨true⟩).projection top x))
  strict x y lower different := by
    apply R.lex_strict (R.lex R) (seed.mono (t.root.projection_mono top lower))
    rcases t.cover y with root | ⟨j, a, eq⟩
    · exact Or.inl (t.root.projected_strict top greatest seed x y lower different root)
    · apply Or.inr
      apply R.lex_strict R (seed.mono ((t.child ⟨false⟩).projection_mono top lower))
      rcases j with ⟨j⟩
      cases j with
      | false => exact Or.inl ((t.child ⟨false⟩).projected_strict top greatest seed
          x y lower different ⟨a, eq⟩)
      | true => exact Or.inr ((t.child ⟨true⟩).projected_strict top greatest seed
          x y lower different ⟨a, eq⟩)

theorem binaryTuple_countable (countable : CountableRange seed.value)
    (t : Tile P (ULift.{u} Unit)) : CountableRange (binaryTuple top greatest R seed t).value :=
  countable_range_pair (countable_range_precompose countable (t.root.projection top))
    (countable_range_precompose countable ((t.child ⟨()⟩).projection top))

theorem rectangleTuple_countable (countable : CountableRange seed.value)
    (t : Tile P (ULift.{u} Bool)) : CountableRange (rectangleTuple top greatest R seed t).value :=
  countable_range_pair (countable_range_precompose countable (t.root.projection top))
    (countable_range_pair
      (countable_range_precompose countable ((t.child ⟨false⟩).projection top))
      (countable_range_precompose countable ((t.child ⟨true⟩).projection top)))

noncomputable def binaryHeight (countable : CountableRange seed.value)
    (t : Tile P (ULift.{u} Unit)) : StrictHeight t.order Rational.order.toHeightOrder :=
  Classical.choose (rational_assignment (R.lex R) (binaryTuple top greatest R seed t)
    (t.root.toFun top) (binaryTuple_countable top greatest R seed countable t))

noncomputable def rectangleHeight (countable : CountableRange seed.value)
    (t : Tile P (ULift.{u} Bool)) : StrictHeight t.order Rational.order.toHeightOrder :=
  Classical.choose (rational_assignment (R.lex (R.lex R)) (rectangleTuple top greatest R seed t)
    (t.root.toFun top) (rectangleTuple_countable top greatest R seed countable t))

end TileRequests.Tile

namespace TileRequests.Request
variable {A : Type u} {H : Type v} {P : MeetOrder A}
    (top : A) (greatest : ∀ a, P.le a top)
    (R : LinearHeightOrder H) (seed : StrictHeight P R.toHeightOrder)
    (countable : CountableRange seed.value)

noncomputable def rationalHeight : (r : Request P) →
    StrictHeight (r.tile top greatest).order Rational.order.toHeightOrder
  | .separation _ => Tile.binaryHeight top greatest R seed countable _
  | .compression _ _ => Tile.binaryHeight top greatest R seed countable _
  | .rectangle _ => Tile.rectangleHeight top greatest R seed countable _

end TileRequests.Request

end Compression.RecursiveMaps



namespace Compression.RecursiveMaps

open RationalHeights
universe u v

namespace PrincipalBatch.Family
variable {A I : Type u} {H : Type v} {P : MeetOrder A} {R : HeightOrder H}
    (b : PrincipalBatch.Family P I) (old : StrictHeight P R)
    (component : ∀ i, StrictHeight (b.order i) R)

def heightValue : b.Node → H
  | .inl x => old.value x
  | .inr x => (component x.1).value x.2.val

def extendHeight
    (above : ∀ x (y : b.Fresh), R.lt (old.value x) ((component y.1).value y.2.val)) :
    StrictHeight b.extension R where
  value := b.heightValue old component
  strict x y lower different := by
    cases x with
    | inl x =>
      cases y with
      | inl y => exact old.strict x y lower (fun eq => different (congrArg Sum.inl eq))
      | inr y => exact above x y
    | inr x =>
      cases y with
      | inl y => exact False.elim lower
      | inr y =>
        rcases lower with inside | impossible
        · rcases x with ⟨i, x, hx⟩
          rcases y with ⟨j, y, hy⟩
          rcases inside with ⟨eq, inside⟩
          cases eq
          apply (component i).strict x y inside
          intro eq
          cases eq
          exact different rfl
        · exact False.elim impossible

end PrincipalBatch.Family

namespace IdealChain
variable (c : IdealChain.{u}) {H : Type v} (R : HeightOrder H)

structure HeightSystem where
  height : ∀ n, StrictHeight (c.order n) R
  step : ∀ n x, (height (n + 1)).value ((c.next n).toFun x) = (height n).value x

namespace HeightSystem
variable {c R} (h : HeightSystem c R)

theorem up {n m : Nat} (lower : n ≤ m) (x : c.Point n) :
    (h.height m).value (c.up lower x) = (h.height n).value x := by
  induction lower with
  | refl => rw [c.up_self]
  | @step m lower ih => rw [c.up_succ lower, h.step, ih]

def value : c.Union → H := Quotient.lift (fun x => (h.height x.1).value x.2) (by
  intro x y related
  rcases related with ⟨k, hx, hy, eq⟩
  exact (h.up hx x.2).symm.trans ((congrArg (h.height k).value eq).trans (h.up hy y.2)))

theorem value_point (n : Nat) (x : c.Point n) :
    h.value (c.point n x) = (h.height n).value x := rfl

def unionHeight : StrictHeight c.unionOrder R where
  value := h.value
  strict x y lower different := by
    rcases c.pair_cover x y with ⟨n, x, y, rfl, rfl⟩
    exact (h.height n).strict x y ((c.le_stage n x y).mp lower)
      (fun eq => different (congrArg (c.point n) eq))

theorem unionHeight_countable (countable : ∀ n, CountableRange (h.height n).value) :
    CountableRange h.unionHeight.value := by
  classical
  let code (n : Nat) : c.Point n → Nat := Classical.choose (countable n)
  have equal (n : Nat) := Classical.choose_spec (countable n)
  let labelValue (x : c.Label) := (h.height x.1).value x.2
  have label_equal (x y : c.Label)
      (eq : natPair x.1 (code x.1 x.2) = natPair y.1 (code y.1 y.2)) :
      labelValue x = labelValue y := by
    rcases x with ⟨n, x⟩
    rcases y with ⟨m, y⟩
    rcases natPair_injective eq with ⟨same, codes⟩
    cases same
    exact equal n x y codes
  have out_value (x : c.Union) : labelValue (Quotient.out x) = h.value x :=
    congrArg h.value (Quotient.out_eq x)
  refine ⟨fun x => natPair (Quotient.out x).1
    (code (Quotient.out x).1 (Quotient.out x).2), ?_⟩
  intro x y eq
  exact (out_value x).symm.trans ((label_equal _ _ eq).trans (out_value y))

end HeightSystem
end IdealChain

namespace RootedGluing.Scheme
variable {V : Type u} {Column : Type v} (d : RootedGluing.Scheme V)
    (C : LinearHeightOrder Column) (column : Nat → Column)
    (increasing : ∀ n, C.lt (column n) (column (n + 1)))
    (seed : StrictHeight (d.order d.root) (lexOrder C).toHeightOrder)
    (seed_bound : ∀ x, C.lt (seed.value x).1 (column 0))
    (localHeight : ∀ v, StrictHeight (d.order v) Rational.order.toHeightOrder)

structure BoundedHeight (n : Nat) where
  height : StrictHeight (d.stages n).order (lexOrder C).toHeightOrder
  bound : ∀ x, C.lt (height.value x).1 (column n)

noncomputable def nextBounded (n : Nat) (old : d.BoundedHeight C column n) :
    d.BoundedHeight C column (n + 1) := {
  height := (d.stages n).batch.extendHeight old.height
    (fun i => {
      value := fun x => (column n, (localHeight i.val).value x)
      strict := fun x y lower different =>
        Or.inr ⟨rfl, (localHeight i.val).strict x y lower different⟩ })
    (fun x _ => Or.inl (old.bound x))
  bound := by
    intro x
    cases x with
    | inl x => exact C.trans (old.bound x) (increasing n)
    | inr x => exact increasing n }

noncomputable def boundedStages : (n : Nat) → d.BoundedHeight C column n
  | 0 => ⟨seed, seed_bound⟩
  | n + 1 => d.nextBounded C column increasing localHeight n (boundedStages n)

noncomputable def heightSystem : d.chain.HeightSystem (lexOrder C).toHeightOrder where
  height n := (d.boundedStages C column increasing seed seed_bound localHeight n).height
  step _ _ := rfl

noncomputable def externalHeight : StrictHeight d.gluedOrder (lexOrder C).toHeightOrder :=
  (d.heightSystem C column increasing seed seed_bound localHeight).unionHeight

theorem externalHeight_stage (n : Nat) (x : (d.stages n).Point) :
    (d.externalHeight C column increasing seed seed_bound localHeight).value (d.chain.point n x) =
      (d.boundedStages C column increasing seed seed_bound localHeight n).height.value x := rfl

theorem externalHeight_original (x : d.Space d.root) :
    (d.externalHeight C column increasing seed seed_bound localHeight).value
      ((d.vertex d.root).toFun x) = seed.value x := by
  rw [d.vertex_at d.root 0 d.depth_root.le]
  rfl

theorem boundedStages_countable (seed_countable : CountableRange seed.value) (n : Nat) :
    CountableRange (d.boundedStages C column increasing seed seed_bound localHeight n).height.value := by
  induction n with
  | zero => exact seed_countable
  | succ n ih =>
    rcases ih with ⟨oldCode, old_equal⟩
    let code : (d.stages (n + 1)).Point → Nat
      | .inl x => 2 * oldCode x
      | .inr x => 2 * Rational.code ((localHeight x.1.val).value x.2.val) + 1
    refine ⟨code, ?_⟩
    intro x y eq
    cases x with
    | inl x =>
      cases y with
      | inl y => exact old_equal x y (by change 2 * oldCode x = 2 * oldCode y at eq; omega)
      | inr y => change 2 * oldCode x = 2 * _ + 1 at eq; omega
    | inr x =>
      cases y with
      | inl y => change 2 * _ + 1 = 2 * oldCode y at eq; omega
      | inr y =>
        change (column n, (localHeight x.1.val).value x.2.val) =
          (column n, (localHeight y.1.val).value y.2.val)
        refine Prod.ext rfl ?_
        apply Rational.code_injective
        change 2 * Rational.code ((localHeight x.1.val).value x.2.val) + 1 =
          2 * Rational.code ((localHeight y.1.val).value y.2.val) + 1 at eq
        dsimp only
        omega

theorem externalHeight_countable (seed_countable : CountableRange seed.value) :
    CountableRange (d.externalHeight C column increasing seed seed_bound localHeight).value :=
  (d.heightSystem C column increasing seed seed_bound localHeight).unionHeight_countable
    (d.boundedStages_countable C column increasing seed seed_bound localHeight seed_countable)

theorem externalHeight_column_bound (cap : Column) (above : ∀ n, C.lt (column n) cap)
    (x : d.Node) :
    C.lt ((d.externalHeight C column increasing seed seed_bound localHeight).value x).1 cap := by
  rcases d.chain.cover x with ⟨n, x, rfl⟩
  exact C.trans ((d.boundedStages C column increasing seed seed_bound localHeight n).bound x) (above n)

end RootedGluing.Scheme

end Compression.RecursiveMaps

end PartitionPilot

end OAI
