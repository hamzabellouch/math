import OAI.SetTheory.PartitionPrinciple.Definability.ExternalWordRewriteRelations

namespace OAI


namespace PartitionPilot.Compression.RecursiveMaps

namespace CosetGeometry

universe u

variable (J S : Type u) [Group J]

def Same (x y : External J S) : Prop := ∃ j, x * old J S j = y

def cosetSetoid : Setoid (External J S) where
  r := Same J S
  iseqv := by
    constructor
    · intro x
      exact ⟨1, by rw [map_one, mul_one]⟩
    · rintro x y ⟨j, rfl⟩
      exact ⟨j⁻¹, by rw [map_inv, mul_inv_cancel_right]⟩
    · rintro x y z ⟨i, rfl⟩ ⟨j, rfl⟩
      exact ⟨i * j, by rw [map_mul, mul_assoc]⟩

def Vertex := Quotient (cosetSetoid J S)
def point (g : External J S) : Vertex J S := Quotient.mk (cosetSetoid J S) g

def root : Vertex J S := point J S 1

theorem point_eq (g h : External J S) : point J S g = point J S h ↔ ∃ j, g * old J S j = h :=
  ⟨fun eq => Quotient.exact eq, fun eq => Quotient.sound eq⟩

theorem root_eq_point (g : External J S) : root J S = point J S g ↔ ∃ j, old J S j = g := by
  rw [root, point_eq]
  simp only [one_mul]

def act (g : External J S) : Vertex J S → Vertex J S :=
  Quotient.map (fun x => g * x) (by
    rintro x y ⟨j, rfl⟩
    exact ⟨j, mul_assoc _ _ _⟩)

theorem act_point (g h : External J S) : act J S g (point J S h) = point J S (g * h) := rfl

theorem act_root (g : External J S) : act J S g (root J S) = point J S g := by
  change point J S (g * 1) = _
  rw [mul_one]

theorem act_one (x : Vertex J S) : act J S 1 x = x := by
  induction x using Quotient.ind with
  | _ x => exact congrArg (point J S) (one_mul x)

theorem act_mul (g h : External J S) (x : Vertex J S) :
    act J S (g * h) x = act J S g (act J S h x) := by
  induction x using Quotient.ind with
  | _ x => exact congrArg (point J S) (mul_assoc g h x)

def Dart := (External J S × S) × Bool

def reverse (d : Dart J S) : Dart J S := (d.1, !d.2)

def startRep (d : Dart J S) : External J S :=
  if d.2 then d.1.1 else d.1.1 * generator J S d.1.2

def endRep (d : Dart J S) : External J S :=
  if d.2 then d.1.1 * generator J S d.1.2 else d.1.1

def letter (d : Dart J S) : S × Bool := (d.1.2, d.2)
def source (d : Dart J S) : Vertex J S := point J S (startRep J S d)
def target (d : Dart J S) : Vertex J S := point J S (endRep J S d)

theorem signed_true (s : S) : signed J S (s, true) = generator J S s := rfl

theorem signed_false (s : S) : signed J S (s, false) = (generator J S s)⁻¹ := by
  rw [generator, ← map_inv]
  rfl

theorem end_eq (d : Dart J S) : startRep J S d * signed J S (letter J S d) = endRep J S d := by
  rcases d with ⟨⟨w, s⟩, b⟩
  cases b
  · change (w * generator J S s) * signed J S (s, false) = w
    rw [signed_false, mul_inv_cancel_right]
  · rfl

theorem reverse_reverse (d : Dart J S) : reverse J S (reverse J S d) = d := by
  rcases d with ⟨⟨w, s⟩, b⟩
  cases b <;> rfl

theorem source_reverse (d : Dart J S) : source J S (reverse J S d) = target J S d := by
  rcases d with ⟨⟨w, s⟩, b⟩
  cases b <;> rfl

theorem target_reverse (d : Dart J S) : target J S (reverse J S d) = source J S d := by
  rcases d with ⟨⟨w, s⟩, b⟩
  cases b <;> rfl

theorem cancellation_reverses_edge (d e : Dart J S)
    (joined : startRep J S e = endRep J S d)
    (cancel : Cancel S (letter J S d) (letter J S e)) : e = reverse J S d := by
  rcases d with ⟨⟨w, s⟩, b⟩
  rcases e with ⟨⟨v, t⟩, c⟩
  cases b <;> cases c
  · simp [Cancel, letter] at cancel
  · have st : s = t := cancel.1
    subst t
    change v = w at joined
    subst v
    rfl
  · have st : s = t := cancel.1
    subst t
    change v * generator J S s = w * generator J S s at joined
    have vw := mul_right_cancel joined
    subst v
    rfl
  · simp [Cancel, letter] at cancel

def translate (g : External J S) (d : Dart J S) : Dart J S := ((g * d.1.1, d.1.2), d.2)

theorem source_translate (g : External J S) (d : Dart J S) :
    source J S (translate J S g d) = act J S g (source J S d) := by
  rcases d with ⟨⟨w, s⟩, b⟩
  cases b
  · exact congrArg (point J S) (mul_assoc g w (generator J S s))
  · rfl

theorem target_translate (g : External J S) (d : Dart J S) :
    target J S (translate J S g d) = act J S g (target J S d) := by
  rcases d with ⟨⟨w, s⟩, b⟩
  cases b
  · rfl
  · exact congrArg (point J S) (mul_assoc g w (generator J S s))

inductive Follows : Vertex J S → List (Dart J S) → Vertex J S → Prop
  | nil (v) : Follows v [] v
  | cons (d : Dart J S) {L v} (tail : Follows (target J S d) L v) :
      Follows (source J S d) (d :: L) v

theorem follows_cons_source {v w : Vertex J S} {d : Dart J S} {L}
    (path : Follows J S v (d :: L) w) : v = source J S d := by
  cases path
  rfl

theorem follows_tail {v w : Vertex J S} {d : Dart J S} {L}
    (path : Follows J S v (d :: L) w) : Follows J S (target J S d) L w := by
  cases path with
  | cons _ tail => exact tail

theorem follows_append {v w z : Vertex J S} {L M}
    (first : Follows J S v L w) (second : Follows J S w M z) :
    Follows J S v (L ++ M) z := by
  induction first with
  | nil => exact second
  | cons d tail ih => exact Follows.cons d (ih second)

theorem follows_translate {v w : Vertex J S} {L} (path : Follows J S v L w)
    (g : External J S) :
    Follows J S (act J S g v) (L.map (translate J S g)) (act J S g w) := by
  induction path with
  | nil v => exact Follows.nil _
  | cons d tail ih =>
    rw [← source_translate, List.map_cons]
    apply Follows.cons
    rw [target_translate]
    exact ih







def NoBacktracking : List (Dart J S) → Prop
  | [] => True
  | [_] => True
  | d :: e :: rest => e ≠ reverse J S d ∧ NoBacktracking (e :: rest)

theorem follows_empty_eq {v w : Vertex J S} {L : List (Dart J S)}
    (path : Follows J S v L w) (empty : L = []) : v = w := by
  induction path with
  | nil => rfl
  | cons d tail ih => cases empty

theorem follows_singleton_target {v w : Vertex J S} {d : Dart J S}
    (path : Follows J S v [d] w) : w = target J S d := by
  have tail : Follows J S (target J S d) [] w := follows_tail J S path
  exact (follows_empty_eq J S tail rfl).symm

theorem path_word (d : Dart J S) (tail : List (Dart J S)) (finish : Vertex J S)
    (path : Follows J S (source J S d) (d :: tail) finish)
    (reduced : NoBacktracking J S (d :: tail)) :
    ∃ j rest, Reduced J S ((letter J S d, j) :: rest) ∧
      point J S (startRep J S d * eval J S ((letter J S d, j) :: rest)) = finish := by
  induction tail generalizing d finish with
  | nil =>
    refine ⟨1, [], True.intro, ?_⟩
    rw [follows_singleton_target J S path]
    change point J S (startRep J S d * (signed J S (letter J S d) * old J S 1 * 1)) = _
    rw [map_one, mul_one, mul_one, end_eq]
    rfl
  | cons e tail ih =>
    have ep := follows_tail J S path
    have join : target J S d = source J S e := follows_cons_source J S ep
    rw [join] at ep
    rcases ih e finish ep reduced.2 with ⟨k, rest, ereduced, endpoint⟩
    rcases (point_eq J S (endRep J S d) (startRep J S e)).mp join with ⟨j, coordinate⟩
    refine ⟨j, (letter J S e, k) :: rest, ⟨?_, ereduced⟩, ?_⟩
    · intro jone cancel
      change j = 1 at jone
      have joined : startRep J S e = endRep J S d := by
        rw [jone, map_one, mul_one] at coordinate
        exact coordinate.symm
      exact reduced.1 (cancellation_reverses_edge J S d e joined cancel)
    · have transition : startRep J S d * signed J S (letter J S d) * old J S j = startRep J S e :=
        (congrArg (fun x => x * old J S j) (end_eq J S d)).trans coordinate
      calc
        point J S (startRep J S d * eval J S ((letter J S d, j) :: (letter J S e, k) :: rest)) =
            point J S ((startRep J S d * signed J S (letter J S d) * old J S j) *
              eval J S ((letter J S e, k) :: rest)) := by simp only [eval, mul_assoc]
        _ = point J S (startRep J S e * eval J S ((letter J S e, k) :: rest)) := by rw [transition]
        _ = finish := endpoint

theorem no_closed_reduced_path (v : Vertex J S) (d : Dart J S) (tail : List (Dart J S))
    (path : Follows J S v (d :: tail) v) : ¬ NoBacktracking J S (d :: tail) := by
  classical
  intro reduced
  have start := follows_cons_source J S path
  rw [start] at path
  rcases path_word J S d tail (source J S d) path reduced with ⟨j, rest, normal, endpoint⟩
  let value := eval J S ((letter J S d, j) :: rest)
  rcases (point_eq J S (startRep J S d * value) (startRep J S d)).mp endpoint with ⟨k, eq⟩
  have cancelled : value * old J S k = 1 := by
    apply mul_left_cancel (a := startRep J S d)
    simpa only [mul_assoc, mul_one] using eq
  have value_eq : value = old J S k⁻¹ := by
    calc
      value = value * (old J S k * old J S k⁻¹) := by rw [map_inv, mul_inv_cancel, mul_one]
      _ = (value * old J S k) * old J S k⁻¹ := (mul_assoc _ _ _).symm
      _ = old J S k⁻¹ := by rw [cancelled, one_mul]
  exact reduced_not_old J S (letter J S d) j rest normal k⁻¹ value_eq

def Reachable (g : External J S) : Prop :=
  ∃ L, Follows J S (root J S) L (point J S g)

theorem reachable_one : Reachable J S 1 := ⟨[], Follows.nil _⟩

theorem reachable_old (j : J) : Reachable J S (old J S j) := by
  have eq := (root_eq_point J S (old J S j)).mpr ⟨j, rfl⟩
  refine ⟨[], ?_⟩
  rw [← eq]
  exact Follows.nil _

theorem reachable_mul {g h : External J S} (hg : Reachable J S g) (hh : Reachable J S h) :
    Reachable J S (g * h) := by
  rcases hg with ⟨L, first⟩
  rcases hh with ⟨M, second⟩
  have shifted := follows_translate J S second g
  rw [act_root, act_point] at shifted
  exact ⟨L ++ M.map (translate J S g), follows_append J S first shifted⟩

theorem reachable_generator (s : S) : Reachable J S (generator J S s) := by
  let d : Dart J S := ((1, s), true)
  have path := Follows.cons d (Follows.nil (target J S d))
  change Follows J S (root J S) [d] (point J S (1 * generator J S s)) at path
  rw [one_mul] at path
  exact ⟨[d], path⟩

theorem reachable_generator_inv (s : S) : Reachable J S (generator J S s)⁻¹ := by
  let d : Dart J S := (((generator J S s)⁻¹, s), false)
  have path := Follows.cons d (Follows.nil (target J S d))
  change Follows J S (point J S ((generator J S s)⁻¹ * generator J S s)) [d]
    (point J S (generator J S s)⁻¹) at path
  rw [inv_mul_cancel] at path
  exact ⟨[d], path⟩

theorem reachable_free (f : FreeGroup S) : Reachable J S (free J S f) := by
  induction f using FreeGroup.induction_on with
  | one => rw [map_one]; exact reachable_one J S
  | of letter => exact reachable_generator J S letter
  | inv_of letter _ => rw [map_inv]; exact reachable_generator_inv J S letter
  | mul first second firstReachable secondReachable =>
    rw [map_mul]
    exact reachable_mul J S firstReachable secondReachable

theorem reachable_element (g : External J S) : Reachable J S g := by
  induction g using Monoid.CoprodI.induction_on with
  | one => exact reachable_one J S
  | of i x =>
    cases i
    · exact reachable_old J S x
    · exact reachable_free J S x
  | mul x y hx hy => exact reachable_mul J S hx hy

theorem connected (v : Vertex J S) : ∃ L, Follows J S (root J S) L v := by
  induction v using Quotient.ind with
  | _ g => exact reachable_element J S g

def IsIndexedTree : Prop :=
  (∀ v : Vertex J S, ∃ L, Follows J S (root J S) L v) ∧
  ∀ v d tail, Follows J S v (d :: tail) v → ¬ NoBacktracking J S (d :: tail)

theorem coset_tree : IsIndexedTree J S :=
  ⟨connected J S, no_closed_reduced_path J S⟩

theorem reversal_of_not_reduced (L : List (Dart J S)) (h : ¬ NoBacktracking J S L) :
    ∃ pre d suffix, L = pre ++ d :: reverse J S d :: suffix := by
  classical
  induction L with
  | nil => exact False.elim (h True.intro)
  | cons d tail ih =>
    cases tail with
    | nil => exact False.elim (h True.intro)
    | cons e tail =>
      by_cases back : e = reverse J S d
      · exact ⟨[], d, tail, by rw [back]; rfl⟩
      · rcases ih (fun ht => h ⟨back, ht⟩) with ⟨pre, x, suffix, eq⟩
        exact ⟨d :: pre, x, suffix, congrArg (List.cons d) eq⟩

theorem closed_path_has_reversal (v : Vertex J S) (d : Dart J S) (tail : List (Dart J S))
    (path : Follows J S v (d :: tail) v) :
    ∃ pre e suffix, d :: tail = pre ++ e :: reverse J S e :: suffix :=
  reversal_of_not_reduced J S _ (no_closed_reduced_path J S v d tail path)

@[instance_reducible]
def groupOfData {G : Type u} (g : GroupData G) : Group G where
  mul := g.mul
  mul_assoc := g.assoc
  one := g.one
  one_mul := g.one_mul
  mul_one := g.mul_one
  inv := g.inv
  inv_mul_cancel := g.inv_mul

theorem taskSystem_coset_tree {A G Task Label : Type u} {P : MeetOrder A}
    (f : TaskSystem P G Task Label) (Letters : Type u) :
    @IsIndexedTree G Letters (groupOfData f.group) := by
  let : Group G := groupOfData f.group
  exact coset_tree G Letters

end CosetGeometry



section

namespace EdgeWords

universe u
variable {E : Type u}

def reverse (d : E × Bool) : E × Bool := (d.1, !d.2)

def NoBacktracking : List (E × Bool) → Prop
  | [] => True
  | [_] => True
  | d :: e :: rest => e ≠ reverse d ∧ NoBacktracking (e :: rest)

theorem mk_cons (d : E × Bool) (L : List (E × Bool)) :
    FreeGroup.mk (d :: L) = FreeGroup.mk [d] * FreeGroup.mk L :=
  (@FreeGroup.mul_mk E [d] L).symm

theorem mk_reverse (d : E × Bool) :
    FreeGroup.mk [reverse d] = (FreeGroup.mk [d])⁻¹ := by
  rcases d with ⟨e, b⟩
  cases b <;> rfl

theorem mk_delete_reversal (pre : List (E × Bool)) (d : E × Bool) (suffix) :
    FreeGroup.mk (pre ++ d :: reverse d :: suffix) = FreeGroup.mk (pre ++ suffix) :=
  Quot.sound FreeGroup.Red.Step.not

theorem reduce_of_no_backtracking [DecidableEq E] (L : List (E × Bool))
    (h : NoBacktracking L) : FreeGroup.reduce L = L := by
  induction L with
  | nil => rfl
  | cons d tail ih =>
    cases tail with
    | nil => rfl
    | cons e rest =>
      rw [FreeGroup.reduce.cons, ih h.2]
      have safe : ¬ (d.1 = e.1 ∧ d.2 = !e.2) := by
        rintro ⟨edges, signs⟩
        apply h.1
        change e = (d.1, !d.2)
        refine Prod.ext edges.symm ?_
        have flipped := congrArg Bool.not signs
        simpa only [Bool.not_not] using flipped.symm
      change (if d.1 = e.1 ∧ d.2 = !e.2 then rest else d :: e :: rest) = _
      rw [ite_eq_right safe]

theorem reduced_word_eq_one_iff (L : List (E × Bool)) (h : NoBacktracking L) :
    FreeGroup.mk L = 1 ↔ L = [] := by
  classical
  constructor
  · intro eq
    have words := congrArg FreeGroup.toWord eq
    simpa only [FreeGroup.toWord_mk, FreeGroup.toWord_one,
      reduce_of_no_backtracking L h] using words
  · rintro rfl
    rfl

end EdgeWords

namespace CosetGeometry

universe u
variable (J S : Type u) [Group J]

theorem follows_delete_reversal (pre : List (Dart J S)) (d : Dart J S) (suffix)
    {v w : Vertex J S} (path : Follows J S v (pre ++ d :: reverse J S d :: suffix) w) :
    Follows J S v (pre ++ suffix) w := by
  induction pre generalizing v with
  | nil =>
    have start := follows_cons_source J S path
    have tail := follows_tail J S (follows_tail J S path)
    rw [target_reverse] at tail
    rw [start]
    exact tail
  | cons e pre ih =>
    have start := follows_cons_source J S path
    rw [start]
    exact Follows.cons e (ih (follows_tail J S path))

theorem closed_edge_word (v : Vertex J S) (L : List (Dart J S))
    (path : Follows J S v L v) : FreeGroup.mk L = 1 := by
  cases hL : L with
  | nil => rfl
  | cons d tail =>
    rw [hL] at path
    rcases closed_path_has_reversal J S v d tail path with ⟨pre, e, suffix, eq⟩
    have cut : Follows J S v (pre ++ suffix) v := by
      apply follows_delete_reversal J S pre e suffix
      rw [← eq]
      exact path
    calc
      FreeGroup.mk (d :: tail) = FreeGroup.mk (pre ++ suffix) := by
        erw [eq]
        exact EdgeWords.mk_delete_reversal pre e suffix
      _ = 1 := closed_edge_word v (pre ++ suffix) cut
termination_by L.length
decreasing_by
  rw [hL]
  have lengths := congrArg List.length eq
  simp only [List.length_cons, List.length_append] at lengths ⊢
  omega

end CosetGeometry
end



namespace CosetGeometry.TileStars

universe u
variable (J S R : Type u) [Group J]

abbrev Center := External J S × R
abbrev OldEdge := External J S × S
def Vertex := Sum (CosetGeometry.Vertex J S) (Center J S R)
def Edge := Sum (Center J S R) (OldEdge J S)
abbrev Dart := Edge J S R × Bool

def reverse (d : Dart J S R) : Dart J S R := EdgeWords.reverse d

variable (request : S → R)

def centerOf (e : OldEdge J S) : Center J S R := (e.1, request e.2)

def source (d : Dart J S R) : Vertex J S R :=
  match d.1, d.2 with
  | .inl c, true => .inl (point J S c.1)
  | .inl c, false => .inr c
  | .inr e, true => .inr (centerOf J S R request e)
  | .inr e, false => .inl (point J S (e.1 * generator J S e.2))

def target (d : Dart J S R) : Vertex J S R :=
  source J S R request (reverse J S R d)

theorem reverse_reverse (d : Dart J S R) : reverse J S R (reverse J S R d) = d := by
  rcases d with ⟨e, b⟩
  cases b <;> rfl

theorem source_reverse (d : Dart J S R) :
    source J S R request (reverse J S R d) = target J S R request d := rfl

theorem target_reverse (d : Dart J S R) :
    target J S R request (reverse J S R d) = source J S R request d := by
  exact congrArg (source J S R request) (reverse_reverse J S R d)

def root : Vertex J S R := .inl (CosetGeometry.root J S)

inductive Follows : Vertex J S R → List (Dart J S R) → Vertex J S R → Prop
  | nil (v) : Follows v [] v
  | cons (d : Dart J S R) {L v}
      (tail : Follows (target J S R request d) L v) :
      Follows (source J S R request d) (d :: L) v

theorem follows_append {v w z : Vertex J S R} {L M}
    (first : Follows J S R request v L w) (second : Follows J S R request w M z) :
    Follows J S R request v (L ++ M) z := by
  induction first with
  | nil => exact second
  | cons d tail ih => exact Follows.cons d (ih second)

def contract : Vertex J S R → CosetGeometry.Vertex J S
  | .inl v => v
  | .inr c => point J S c.1

def projectDart (d : Dart J S R) : List (CosetGeometry.Dart J S) :=
  match d.1 with
  | .inl _ => []
  | .inr e => [(e, d.2)]

def project (L : List (Dart J S R)) : List (CosetGeometry.Dart J S) :=
  L.flatMap (projectDart J S R)

theorem contract_edge (d : Dart J S R) :
    CosetGeometry.Follows J S (contract J S R (source J S R request d))
      (projectDart J S R d) (contract J S R (target J S R request d)) := by
  rcases d with ⟨c | e, b⟩ <;> cases b
  · exact CosetGeometry.Follows.nil _
  · exact CosetGeometry.Follows.nil _
  · exact CosetGeometry.Follows.cons (e, false) (CosetGeometry.Follows.nil _)
  · exact CosetGeometry.Follows.cons (e, true) (CosetGeometry.Follows.nil _)

theorem follows_project {v w : Vertex J S R} {L}
    (path : Follows J S R request v L w) :
    CosetGeometry.Follows J S (contract J S R v) (project J S R L) (contract J S R w) := by
  induction path with
  | nil v => exact CosetGeometry.Follows.nil _
  | cons d tail ih =>
    exact CosetGeometry.follows_append J S (contract_edge J S R request d) ih

def expandDart (d : CosetGeometry.Dart J S) : List (Dart J S R) :=
  if d.2 then
    [(.inl (centerOf J S R request d.1), true), (.inr d.1, true)]
  else
    [(.inr d.1, false), (.inl (centerOf J S R request d.1), false)]

theorem expand_edge (d : CosetGeometry.Dart J S) :
    Follows J S R request (.inl (CosetGeometry.source J S d))
      (expandDart J S R request d) (.inl (CosetGeometry.target J S d)) := by
  rcases d with ⟨e, b⟩
  cases b
  · exact Follows.cons (.inr e, false)
      (Follows.cons (.inl (centerOf J S R request e), false) (Follows.nil _))
  · exact Follows.cons (.inl (centerOf J S R request e), true)
      (Follows.cons (.inr e, true) (Follows.nil _))

theorem follows_expand {v w : CosetGeometry.Vertex J S} {L}
    (path : CosetGeometry.Follows J S v L w) :
    Follows J S R request (.inl v) (L.flatMap (expandDart J S R request)) (.inl w) := by
  induction path with
  | nil v => exact Follows.nil _
  | cons d tail ih => exact follows_append J S R request (expand_edge J S R request d) ih

theorem connected (v : Vertex J S R) :
    ∃ L, Follows J S R request (root J S R) L v := by
  cases v with
  | inl v =>
    rcases CosetGeometry.connected J S v with ⟨L, path⟩
    exact ⟨L.flatMap (expandDart J S R request), follows_expand J S R request path⟩
  | inr c =>
    rcases CosetGeometry.connected J S (point J S c.1) with ⟨L, path⟩
    have lifted := follows_expand J S R request path
    have stem := Follows.cons (J := J) (S := S) (R := R) (request := request)
      (.inl c, true) (Follows.nil _)
    exact ⟨_, follows_append J S R request lifted stem⟩

end CosetGeometry.TileStars



namespace CosetGeometry.TileStars

universe u
variable (J S R : Type u) [Group J] (request : S → R)

def potential : Vertex J S R → FreeGroup (Edge J S R)
  | .inl _ => 1
  | .inr c => FreeGroup.of (.inl c)

def expandHom : FreeGroup (OldEdge J S) →* FreeGroup (Edge J S R) :=
  FreeGroup.lift (fun e =>
    FreeGroup.of (.inl (centerOf J S R request e)) * FreeGroup.of (.inr e))

theorem edge_word (d : Dart J S R) :
    FreeGroup.mk [d] =
      (potential J S R (source J S R request d))⁻¹ *
        expandHom J S R request (FreeGroup.mk (projectDart J S R d)) *
          potential J S R (target J S R request d) := by
  rcases d with ⟨c | e, b⟩ <;> cases b
  · change (FreeGroup.of (.inl c : Edge J S R))⁻¹ =
      (FreeGroup.of (.inl c))⁻¹ * expandHom J S R request 1 * 1
    erw [map_one, mul_one, mul_one]
    rfl
  · change FreeGroup.of (.inl c : Edge J S R) =
      (1 : FreeGroup (Edge J S R))⁻¹ * expandHom J S R request 1 * FreeGroup.of (.inl c)
    erw [map_one, inv_one, one_mul]
    rfl
  · change (FreeGroup.of (.inr e : Edge J S R))⁻¹ =
      (1 : FreeGroup (Edge J S R))⁻¹ * expandHom J S R request (FreeGroup.of e)⁻¹ *
        FreeGroup.of (.inl (centerOf J S R request e))
    rw [inv_one, one_mul, map_inv]
    rw [expandHom, FreeGroup.lift_apply_of]
    change (FreeGroup.of (.inr e : Edge J S R))⁻¹ =
      (FreeGroup.of (.inl (centerOf J S R request e)) * FreeGroup.of (.inr e))⁻¹ *
        FreeGroup.of (.inl (centerOf J S R request e))
    rw [mul_inv_rev, inv_mul_cancel_right]
  · change FreeGroup.of (.inr e : Edge J S R) =
      (FreeGroup.of (.inl (centerOf J S R request e)))⁻¹ *
        expandHom J S R request (FreeGroup.of e) * 1
    rw [expandHom, FreeGroup.lift_apply_of]
    change FreeGroup.of (.inr e : Edge J S R) =
      (FreeGroup.of (.inl (centerOf J S R request e)))⁻¹ *
        (FreeGroup.of (.inl (centerOf J S R request e)) * FreeGroup.of (.inr e)) * 1
    rw [inv_mul_cancel_left, mul_one]

theorem path_word {v w : Vertex J S R} {L}
    (path : Follows J S R request v L w) :
    FreeGroup.mk L = (potential J S R v)⁻¹ *
      expandHom J S R request (FreeGroup.mk (project J S R L)) * potential J S R w := by
  induction path with
  | nil v =>
    change 1 = (potential J S R v)⁻¹ * expandHom J S R request 1 * potential J S R v
    rw [map_one, mul_one, inv_mul_cancel]
  | @cons d L w tail ih =>
    rw [EdgeWords.mk_cons, edge_word, ih]
    change (_ * expandHom J S R request (FreeGroup.mk (projectDart J S R d)) * _) *
      (_ * expandHom J S R request (FreeGroup.mk (project J S R L)) * _) =
      _ * expandHom J S R request (FreeGroup.mk (projectDart J S R d ++ project J S R L)) * _
    erw [← FreeGroup.mul_mk, map_mul]
    simp only [mul_assoc, mul_inv_cancel_left]

theorem closed_edge_word (v : Vertex J S R) (L : List (Dart J S R))
    (path : Follows J S R request v L v) : FreeGroup.mk L = 1 := by
  have equation := path_word J S R request path
  have contracted := CosetGeometry.closed_edge_word J S (contract J S R v)
    (project J S R L) (follows_project J S R request path)
  rw [contracted, map_one, mul_one, inv_mul_cancel] at equation
  exact equation

theorem no_closed_reduced_path (v : Vertex J S R) (d : Dart J S R) (tail)
    (path : Follows J S R request v (d :: tail) v) : ¬ EdgeWords.NoBacktracking (d :: tail) := by
  intro reduced
  have empty := (EdgeWords.reduced_word_eq_one_iff (d :: tail) reduced).mp
    (closed_edge_word J S R request v (d :: tail) path)
  cases empty

def IsIndexedTree : Prop :=
  (∀ v : Vertex J S R, ∃ L, Follows J S R request (root J S R) L v) ∧
  ∀ v d tail, Follows J S R request v (d :: tail) v → ¬ EdgeWords.NoBacktracking (d :: tail)

theorem tile_star_tree : IsIndexedTree J S R request :=
  ⟨connected J S R request, no_closed_reduced_path J S R request⟩

theorem reversal_of_not_reduced (L : List (Dart J S R)) (h : ¬ EdgeWords.NoBacktracking L) :
    ∃ pre d suffix, L = pre ++ d :: reverse J S R d :: suffix := by
  classical
  induction L with
  | nil => exact False.elim (h True.intro)
  | cons d tail ih =>
    cases tail with
    | nil => exact False.elim (h True.intro)
    | cons e tail =>
      by_cases back : e = reverse J S R d
      · exact ⟨[], d, tail, by rw [back]; rfl⟩
      · rcases ih (fun ht => h ⟨back, ht⟩) with ⟨pre, x, suffix, eq⟩
        exact ⟨d :: pre, x, suffix, congrArg (List.cons d) eq⟩

theorem closed_path_has_reversal (v : Vertex J S R) (d : Dart J S R) (tail)
    (path : Follows J S R request v (d :: tail) v) :
    ∃ pre e suffix, d :: tail = pre ++ e :: reverse J S R e :: suffix :=
  reversal_of_not_reduced J S R _ (no_closed_reduced_path J S R request v d tail path)

theorem requested_tile_tree (Children : R → Type u) :
    IsIndexedTree J (Sigma Children) R Sigma.fst :=
  tile_star_tree J (Sigma Children) R Sigma.fst

theorem taskSystem_tile_tree {A G Task Label : Type u} {P : MeetOrder A}
    (f : TaskSystem P G Task Label) (Requests : Type u) (Children : Requests → Type u) :
    @IsIndexedTree G (Sigma Children) Requests (groupOfData f.group) Sigma.fst := by
  let : Group G := groupOfData f.group
  exact requested_tile_tree G Requests Children

end CosetGeometry.TileStars



section

namespace EdgeWords

universe u
variable {E : Type u}

theorem reduced_words_injective {L M : List (E × Bool)}
    (hL : NoBacktracking L) (hM : NoBacktracking M)
    (eq : FreeGroup.mk L = FreeGroup.mk M) : L = M := by
  classical
  have words := congrArg FreeGroup.toWord eq
  simpa only [FreeGroup.toWord_mk, reduce_of_no_backtracking L hL,
    reduce_of_no_backtracking M hM] using words

theorem no_backtracking_append_left (L M : List (E × Bool))
    (h : NoBacktracking (L ++ M)) : NoBacktracking L := by
  induction L with
  | nil => exact True.intro
  | cons d tail ih =>
    cases tail with
    | nil => exact True.intro
    | cons e tail => exact ⟨h.1, ih h.2⟩

end EdgeWords

namespace CosetGeometry.TileStars

universe u
variable (J S R : Type u) [Group J] (request : S → R)

theorem follows_cons_source {v w : Vertex J S R} {d : Dart J S R} {L}
    (path : Follows J S R request v (d :: L) w) : v = source J S R request d := by
  cases path
  rfl

theorem follows_tail {v w : Vertex J S R} {d : Dart J S R} {L}
    (path : Follows J S R request v (d :: L) w) :
    Follows J S R request (target J S R request d) L w := by
  cases path with
  | cons _ tail => exact tail

theorem follows_delete_reversal (pre : List (Dart J S R)) (d : Dart J S R) (suffix)
    {v w : Vertex J S R}
    (path : Follows J S R request v (pre ++ d :: reverse J S R d :: suffix) w) :
    Follows J S R request v (pre ++ suffix) w := by
  induction pre generalizing v with
  | nil =>
    have start := follows_cons_source J S R request path
    have tail := follows_tail J S R request (follows_tail J S R request path)
    rw [target_reverse] at tail
    rw [start]
    exact tail
  | cons e pre ih =>
    have start := follows_cons_source J S R request path
    rw [start]
    exact Follows.cons e (ih (follows_tail J S R request path))

theorem reduced_path {v w : Vertex J S R} (L : List (Dart J S R))
    (path : Follows J S R request v L w) :
    ∃ M, Follows J S R request v M w ∧ EdgeWords.NoBacktracking M ∧ M.length ≤ L.length := by
  classical
  by_cases reduced : EdgeWords.NoBacktracking L
  · exact ⟨L, path, reduced, le_refl _⟩
  · rcases reversal_of_not_reduced J S R L reduced with ⟨pre, d, suffix, eq⟩
    have cut : Follows J S R request v (pre ++ suffix) w := by
      apply follows_delete_reversal J S R request pre d suffix
      rw [← eq]
      exact path
    rcases reduced_path (pre ++ suffix) cut with ⟨M, mp, mr, bound⟩
    refine ⟨M, mp, mr, le_trans bound ?_⟩
    rw [eq]
    simp only [List.length_append, List.length_cons]
    omega
termination_by L.length
decreasing_by
  rw [eq]
  simp only [List.length_append, List.length_cons]
  omega

theorem follows_reverse {v w : Vertex J S R} {L}
    (path : Follows J S R request v L w) :
    Follows J S R request w (FreeGroup.invRev L) v := by
  induction path with
  | nil v => exact Follows.nil _
  | @cons d L w tail ih =>
    rw [FreeGroup.invRev_cons]
    apply follows_append J S R request ih
    have last := Follows.cons (J := J) (S := S) (R := R) (request := request)
      (reverse J S R d) (Follows.nil _)
    rw [source_reverse, target_reverse] at last
    exact last

theorem path_words_equal {v w : Vertex J S R} {L M}
    (first : Follows J S R request v L w) (second : Follows J S R request v M w) :
    FreeGroup.mk L = FreeGroup.mk M := by
  have loop := follows_append J S R request first (follows_reverse J S R request second)
  have equation := closed_edge_word J S R request v (L ++ FreeGroup.invRev M) loop
  rw [← FreeGroup.mul_mk, ← FreeGroup.inv_mk] at equation
  exact mul_inv_eq_one.mp equation

theorem reduced_path_unique {v w : Vertex J S R} {L M}
    (first : Follows J S R request v L w) (second : Follows J S R request v M w)
    (hL : EdgeWords.NoBacktracking L) (hM : EdgeWords.NoBacktracking M) : L = M :=
  EdgeWords.reduced_words_injective hL hM (path_words_equal J S R request first second)

theorem unique_root_path (v : Vertex J S R) :
    ∃! L, Follows J S R request (root J S R) L v ∧ EdgeWords.NoBacktracking L := by
  rcases connected J S R request v with ⟨L, path⟩
  rcases reduced_path J S R request L path with ⟨M, mp, mr, _⟩
  exact ⟨M, ⟨mp, mr⟩, fun N hN => reduced_path_unique J S R request hN.1 mp hN.2 mr⟩

noncomputable def rootPath (v : Vertex J S R) : List (Dart J S R) :=
  Classical.choose (unique_root_path J S R request v).exists

theorem rootPath_follows (v : Vertex J S R) :
    Follows J S R request (root J S R) (rootPath J S R request v) v :=
  (Classical.choose_spec (unique_root_path J S R request v).exists).1

theorem rootPath_reduced (v : Vertex J S R) :
    EdgeWords.NoBacktracking (rootPath J S R request v) :=
  (Classical.choose_spec (unique_root_path J S R request v).exists).2

theorem rootPath_eq {v : Vertex J S R} {L}
    (path : Follows J S R request (root J S R) L v) (reduced : EdgeWords.NoBacktracking L) :
    rootPath J S R request v = L :=
  reduced_path_unique J S R request (rootPath_follows J S R request v) path
    (rootPath_reduced J S R request v) reduced

theorem rootPath_root : rootPath J S R request (root J S R) = [] :=
  rootPath_eq J S R request (Follows.nil _) True.intro

noncomputable def depth (v : Vertex J S R) : Nat := (rootPath J S R request v).length

theorem rootPath_shortest {v : Vertex J S R} {L}
    (path : Follows J S R request (root J S R) L v) : depth J S R request v ≤ L.length := by
  rcases reduced_path J S R request L path with ⟨M, mp, mr, bound⟩
  have eq := rootPath_eq J S R request mp mr
  exact (congrArg List.length eq).le.trans bound

theorem follows_empty_eq {v w : Vertex J S R} {L}
    (path : Follows J S R request v L w) (empty : L = []) : v = w := by
  induction path with
  | nil => rfl
  | cons d tail ih => cases empty

theorem rootPath_empty_iff (v : Vertex J S R) :
    rootPath J S R request v = [] ↔ v = root J S R := by
  constructor
  · intro empty
    exact (follows_empty_eq J S R request (rootPath_follows J S R request v) empty).symm
  · rintro rfl
    exact rootPath_root J S R request

theorem follows_last (pre : List (Dart J S R)) (d : Dart J S R) {v w : Vertex J S R}
    (path : Follows J S R request v (pre ++ [d]) w) :
    Follows J S R request v pre (source J S R request d) ∧ target J S R request d = w := by
  induction pre generalizing v with
  | nil =>
    have start := follows_cons_source J S R request path
    have finish := follows_empty_eq J S R request (follows_tail J S R request path) rfl
    rw [start]
    exact ⟨Follows.nil _, finish⟩
  | cons e pre ih =>
    rcases ih (follows_tail J S R request path) with ⟨first, finish⟩
    refine ⟨?_, finish⟩
    rw [follows_cons_source J S R request path]
    exact Follows.cons e first

theorem exists_parent_edge (v : Vertex J S R) (nonroot : v ≠ root J S R) :
    ∃ d : Dart J S R, target J S R request d = v ∧
      rootPath J S R request v = rootPath J S R request (source J S R request d) ++ [d] ∧
      depth J S R request v = depth J S R request (source J S R request d) + 1 := by
  rcases List.eq_nil_or_concat' (rootPath J S R request v) with empty | ⟨pre, d, eq⟩
  · exact False.elim (nonroot ((rootPath_empty_iff J S R request v).mp empty))
  · have path := rootPath_follows J S R request v
    have reduced := rootPath_reduced J S R request v
    rw [eq] at path reduced
    rcases follows_last J S R request pre d path with ⟨first, finish⟩
    have shorter := rootPath_eq J S R request first
      (EdgeWords.no_backtracking_append_left pre [d] reduced)
    refine ⟨d, finish, ?_, ?_⟩
    · rw [eq, shorter]
    · change (rootPath J S R request v).length =
        (rootPath J S R request (source J S R request d)).length + 1
      rw [eq, shorter, List.length_append]
      rfl

end CosetGeometry.TileStars




open Attachment
universe u v w

structure IdealEmbedding {A : Type u} {B : Type v} (P : MeetOrder A) (Q : MeetOrder B)
    extends MeetEmbedding P Q where
  ideal : ∀ a x, Q.le x (toFun a) → ∃ b, toFun b = x

namespace IdealEmbedding

variable {A : Type u} {B : Type v} {C : Type w}
    {P : MeetOrder A} {Q : MeetOrder B} {R : MeetOrder C}

def identity (P : MeetOrder A) : IdealEmbedding P P where
  toMeetEmbedding := (identityIso P).toMeetEmbedding
  ideal _ x _ := ⟨x, rfl⟩

def comp (f : IdealEmbedding P Q) (g : IdealEmbedding Q R) : IdealEmbedding P R where
  toMeetEmbedding := compose f.toMeetEmbedding g.toMeetEmbedding
  ideal a x hx := by
    rcases g.ideal (f.toFun a) x hx with ⟨b, rfl⟩
    rcases f.ideal a b ((g.le_iff _ _).mp hx) with ⟨c, rfl⟩
    exact ⟨c, rfl⟩

def ofOrderMap (f : A → B) (le_iff : ∀ a b, Q.le (f a) (f b) ↔ P.le a b)
    (ideal : ∀ a x, Q.le x (f a) → ∃ b, f b = x) : IdealEmbedding P Q where
  toFun := f
  le_iff := le_iff
  ideal := ideal
  map_meet a b := by
    apply Q.antisymm
    · exact Q.le_meet ((le_iff _ _).mpr (P.meet_le_left a b))
        ((le_iff _ _).mpr (P.meet_le_right a b))
    · rcases ideal a (Q.meet (f a) (f b)) (Q.meet_le_left _ _) with ⟨c, eq⟩
      rw [← eq]
      apply (le_iff _ _).mpr
      apply P.le_meet
      · apply (le_iff _ _).mp
        rw [eq]
        exact Q.meet_le_left _ _
      · apply (le_iff _ _).mp
        rw [eq]
        exact Q.meet_le_right _ _

theorem principal (f : IdealEmbedding P Q) (top : A) (greatest : ∀ a, P.le a top) (x : B) :
    Q.le x (f.toFun top) ↔ ∃ a, f.toFun a = x := by
  constructor
  · exact f.ideal top x
  · rintro ⟨a, rfl⟩
    exact (f.le_iff _ _).mpr (greatest a)

theorem principal_surjective (f : IdealEmbedding P Q) (a : A)
    (x : {x : B // Q.le x (f.toFun a)}) :
    ∃ y : {y : A // P.le y a}, f.toFun y.val = x.val := by
  rcases f.ideal a x.val x.property with ⟨y, eq⟩
  exact ⟨⟨y, (f.le_iff _ _).mp (eq ▸ x.property)⟩, eq⟩

noncomputable def principalIso (f : IdealEmbedding P Q) (a : A) :
    MeetIso (idealOrder P a) (idealOrder Q (f.toFun a)) where
  toFun x := ⟨f.toFun x.val, (f.le_iff _ _).mpr x.property⟩
  le_iff x y := f.le_iff x.val y.val
  map_meet x y := Subtype.ext (f.map_meet x.val y.val)
  inverse x := Classical.choose (f.principal_surjective a x)
  right_inverse x := Subtype.ext (Classical.choose_spec (f.principal_surjective a x))
  left_inverse x := by
    apply Subtype.ext
    apply embedding_injective f.toMeetEmbedding
    exact Classical.choose_spec (f.principal_surjective a _)

noncomputable def projection (f : IdealEmbedding P Q) (top : A) (x : B) : A :=
  Classical.choose (f.ideal top (Q.meet x (f.toFun top)) (Q.meet_le_right _ _))

theorem projection_spec (f : IdealEmbedding P Q) (top : A) (x : B) :
    f.toFun (f.projection top x) = Q.meet x (f.toFun top) :=
  Classical.choose_spec (f.ideal top (Q.meet x (f.toFun top)) (Q.meet_le_right _ _))

theorem greatest_part (f : IdealEmbedding P Q) (top : A)
    (greatest : ∀ a, P.le a top) (x : B) (a : A) :
    Q.le (f.toFun a) x ↔ P.le a (f.projection top x) := by
  rw [← f.le_iff, f.projection_spec]
  constructor
  · intro h
    exact Q.le_meet h ((f.le_iff _ _).mpr (greatest a))
  · intro h
    exact Q.trans h (Q.meet_le_left _ _)

end IdealEmbedding
end



namespace PrincipalBatch

open Attachment
universe u

structure Family {A : Type u} (P : MeetOrder A) (I : Type u) where
  Space : I → Type u
  order : ∀ i, MeetOrder (Space i)
  glue : ∀ i, PrincipalAmalgamation.Input P (order i)

namespace Family

variable {A I : Type u} {P : MeetOrder A} (b : Family P I)

def Fresh := (i : I) × (b.glue i).Fresh
def Node := A ⊕ b.Fresh

def Inside (x y : b.Fresh) : Prop :=
  ∃ h : x.1 = y.1, (b.order x.1).le x.2.val (h.symm ▸ y.2.val)

def data : Data P b.Fresh I where
  component := Sigma.fst
  base i := (b.glue i).leftAnchor
  upper _ _ := False
  upper_up := by intro _ _ _ h _; exact h
  upper_meet := by intro _ _ _ h _; exact h
  base_le_upper := by intro _ _ h; exact False.elim h
  base_not_upper := by intro _ h; exact h
  shadow x := (b.glue x.1).shadow x.2.val
  shadow_le_base x := (b.glue x.1).shadow_le_anchor x.2.val
  inside := b.Inside
  inside_refl x := ⟨rfl, (b.order x.1).refl x.2.val⟩
  inside_trans := by
    rintro ⟨i, x⟩ ⟨j, y⟩ ⟨k, z⟩ ⟨hij, hxy⟩ ⟨hjk, hyz⟩
    cases hij
    cases hjk
    exact ⟨rfl, (b.order i).trans hxy hyz⟩
  inside_antisymm := by
    rintro ⟨i, x⟩ ⟨j, y⟩ ⟨hij, hxy⟩ ⟨hji, hyx⟩
    cases hij
    cases hji
    exact congrArg (Sigma.mk i) (Subtype.ext ((b.order i).antisymm hxy hyx))
  inside_component h := h.choose
  inside_shadow := by
    rintro ⟨i, x⟩ ⟨j, y⟩ ⟨hij, hxy⟩
    cases hij
    exact (b.glue i).shadow_mono hxy

theorem component_meets : ComponentMeets b.data := by
  classical
  rintro ⟨i, x⟩ ⟨j, z⟩ same
  change i = j at same
  cases same
  by_cases old : (b.order i).le ((b.order i).meet x.val z.val) (b.glue i).rightAnchor
  · apply Or.inr
    rintro ⟨k, y⟩ ⟨hki, hyx⟩ ⟨hki', hyz⟩
    cases hki
    cases hki'
    exact y.property ((b.order i).trans ((b.order i).le_meet hyx hyz) old)
  · refine Or.inl ⟨⟨i, ⟨(b.order i).meet x.val z.val, old⟩⟩,
      ⟨rfl, (b.order i).meet_le_left _ _⟩, ⟨rfl, (b.order i).meet_le_right _ _⟩, ?_, ?_⟩
    · rintro ⟨k, y⟩ ⟨hki, hyx⟩ ⟨hki', hyz⟩
      cases hki
      cases hki'
      exact ⟨rfl, (b.order i).le_meet hyx hyz⟩
    · exact (b.glue i).shadow_meet x.val z.val

noncomputable def extension : MeetOrder b.Node := meetOrder b.data b.component_meets

noncomputable def old : IdealEmbedding P b.extension where
  toMeetEmbedding := oldEmbedding b.data b.component_meets
  ideal a x hx := by
    cases x with
    | inl x => exact ⟨x, rfl⟩
    | inr x => exact False.elim hx

def componentMap (i : I) : (b.glue i).Node → b.Node
  | .inl a => .inl a
  | .inr x => .inr ⟨i, x⟩

theorem componentMap_le (i : I) (x y : (b.glue i).Node) :
    b.extension.le (b.componentMap i x) (b.componentMap i y) ↔ (b.glue i).order.le x y := by
  cases x with
  | inl a => cases y <;> exact Iff.rfl
  | inr x =>
    cases y with
    | inl a => exact Iff.rfl
    | inr y =>
      change (b.Inside ⟨i, x⟩ ⟨i, y⟩ ∨ False) ↔ ((b.order i).le x.val y.val ∨ False)
      constructor
      · rintro (⟨h, lower⟩ | impossible)
        · cases h
          exact Or.inl lower
        · exact False.elim impossible
      · rintro (lower | impossible)
        · exact Or.inl ⟨rfl, lower⟩
        · exact False.elim impossible

theorem componentMap_ideal (i : I) (a : (b.glue i).Node) (x : b.Node)
    (lower : b.extension.le x (b.componentMap i a)) :
    ∃ y, b.componentMap i y = x := by
  cases x with
  | inl x => exact ⟨.inl x, rfl⟩
  | inr x =>
    cases a with
    | inl a => exact False.elim lower
    | inr a =>
      rcases lower with h | impossible
      · rcases x with ⟨j, x⟩
        rcases h with ⟨eq, _⟩
        cases eq
        exact ⟨.inr x, rfl⟩
      · exact False.elim impossible

noncomputable def component (i : I) : IdealEmbedding (b.glue i).order b.extension :=
  IdealEmbedding.ofOrderMap (b.componentMap i) (b.componentMap_le i) (b.componentMap_ideal i)

noncomputable def tile (i : I) : IdealEmbedding (b.order i) b.extension :=
  IdealEmbedding.comp
    { toMeetEmbedding := (b.glue i).right, ideal := (b.glue i).right_ideal }
    (b.component i)

theorem tile_old_overlap (i : I) (x : b.Space i) (a : A) :
    (b.tile i).toFun x = b.old.toFun a ↔
      ∃ h : (b.order i).le x (b.glue i).rightAnchor,
        ((b.glue i).overlap.toFun ⟨x, h⟩).val = a := by
  change b.componentMap i ((b.glue i).right.toFun x) = b.componentMap i (.inl a) ↔ _
  exact (Iff.intro (fun h => embedding_injective (b.component i).toMeetEmbedding h)
    (congrArg (b.componentMap i))).trans ((b.glue i).overlap_exact a x)

theorem cover (x : b.Node) :
    (∃ a, b.old.toFun a = x) ∨ ∃ i y, (b.tile i).toFun y = x := by
  cases x with
  | inl a => exact Or.inl ⟨a, rfl⟩
  | inr x =>
    refine Or.inr ⟨x.1, x.2.val, ?_⟩
    exact congrArg (b.componentMap x.1) ((b.glue x.1).represent_new x.2.val x.2.property)

theorem fresh_old_meet (x : b.Fresh) (a : A) :
    b.extension.meet (.inr x) (b.old.toFun a) =
      b.old.toFun (P.meet ((b.glue x.1).shadow x.2.val) a) :=
  meet_eq b.data b.component_meets (Attachment.shadow_meet b.data x a (fun h => h))

theorem fresh_greatest_old_part (x : b.Fresh) (a : A) :
    b.extension.le (b.old.toFun a) (.inr x) ↔ P.le a ((b.glue x.1).shadow x.2.val) := Iff.rfl

theorem different_fresh_incomparable (x y : b.Fresh) (different : x.1 ≠ y.1) :
    ¬ b.extension.le (.inr x) (.inr y) := by
  intro lower
  rcases lower with ⟨same, _⟩ | impossible
  · exact different same
  · exact impossible

theorem old_vertex_preserved {V : Type u} {Q : MeetOrder V} (f : IdealEmbedding Q P) :
    ∃ e : IdealEmbedding Q b.extension, ∀ x, e.toFun x = b.old.toFun (f.toFun x) :=
  ⟨f.comp b.old, fun _ => rfl⟩

theorem tile_vertex_preserved (i : I) {V : Type u} {Q : MeetOrder V}
    (f : IdealEmbedding Q (b.order i)) :
    ∃ e : IdealEmbedding Q b.extension, ∀ x, e.toFun x = (b.tile i).toFun (f.toFun x) :=
  ⟨f.comp (b.tile i), fun _ => rfl⟩

end Family
end PrincipalBatch

end PartitionPilot.Compression.RecursiveMaps

end OAI
