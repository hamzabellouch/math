import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Fintype.Sum
import Mathlib.LinearAlgebra.Matrix.Notation

namespace OAI

noncomputable section

open Classical Set

namespace EilenbergGanea
/-- `false` names x; `true` names y. The second Boolean is the positive sign. -/
def seedWord : Bool → List (Bool × Bool)
  | false => [(false, true), (false, true), (true, false), (true, false),
      (true, false), (true, false), (true, false)]
  | true => [(false, true), (false, true), (true, true), (false, false),
      (true, true), (false, false), (true, true), (false, false)]

/-- Numbers of sectors in the two coned boundary polygons. -/
def boundaryLength (r : Bool) : ℕ := 3 * (seedWord r).length

abbrev RoseVertex := Option (Bool × Fin 2)
abbrev SeedVertex := RoseVertex ⊕ Bool
abbrev CircleEdge := Bool × Fin 3
abbrev Sector := (r : Bool) × Fin (boundaryLength r)
abbrev SeedEdge := CircleEdge ⊕ Sector
abbrev SeedCell := SeedVertex ⊕ (SeedEdge ⊕ Sector)

def circleStart (e : CircleEdge) : RoseVertex :=
  ![none, some (e.1, 0), some (e.1, 1)] e.2

def circleEnd (e : CircleEdge) : RoseVertex :=
  ![some (e.1, 0), some (e.1, 1), none] e.2

def sectorLetter (s : Sector) : Bool × Bool :=
  (seedWord s.1).get ⟨s.2.val / 3, by
    have h := s.2.isLt
    dsimp [boundaryLength] at h
    omega⟩

def sectorCircleEdge (s : Sector) : CircleEdge :=
  ((sectorLetter s).1, if (sectorLetter s).2 then
    ⟨s.2.val % 3, Nat.mod_lt _ (by decide)⟩ else
    ⟨2 - s.2.val % 3, by omega⟩)

def sectorStart (s : Sector) : RoseVertex :=
  if (sectorLetter s).2 then circleStart (sectorCircleEdge s)
  else circleEnd (sectorCircleEdge s)

def nextSector (s : Sector) : Sector :=
  ⟨s.1, ⟨(s.2.val + 1) % boundaryLength s.1,
    Nat.mod_lt _ (by have := s.2.isLt; omega)⟩⟩

def edgeVertices : SeedEdge → Finset SeedVertex
  | .inl e => {.inl (circleStart e), .inl (circleEnd e)}
  | .inr s => {.inr s.1, .inl (sectorStart s)}

def sectorEdges (s : Sector) : Finset SeedEdge :=
  {.inl (sectorCircleEdge s), .inr s, .inr (nextSector s)}

def sectorVertices (s : Sector) : Finset SeedVertex :=
  (sectorEdges s).biUnion edgeVertices

/-- Proper cell-face incidence, including vertices of closed triangles. -/
def properFace : SeedCell → SeedCell → Prop
  | .inl v, .inr (.inl e) => v ∈ edgeVertices e
  | .inl v, .inr (.inr s) => v ∈ sectorVertices s
  | .inr (.inl e), .inr (.inr s) => e ∈ sectorEdges s
  | _, _ => False

def seedGraph : SimpleGraph SeedCell where
  Adj a b := properFace a b ∨ properFace b a
  symm := ⟨fun _ _ h => h.elim Or.inr Or.inl⟩
  loopless := ⟨by
    intro a
    rcases a with a | a
    · simp [properFace]
    · rcases a with a | a <;> simp [properFace]⟩


end EilenbergGanea

namespace EilenbergGanea

/-- The vertex of the rose common to its two circles. -/
def seedBase : SeedCell := .inl (.inl none)

theorem seed_vertex_edge_adj {v : SeedVertex} {e : SeedEdge} (h : v ∈ edgeVertices e) :
    seedGraph.Adj (.inl v) (.inr (.inl e)) := Or.inl h

theorem seed_edge_sector_adj {e : SeedEdge} {s : Sector} (h : e ∈ sectorEdges s) :
    seedGraph.Adj (.inr (.inl e)) (.inr (.inr s)) := Or.inl h

theorem rose_vertex_reachable (v : RoseVertex) :
    seedGraph.Reachable seedBase (.inl (.inl v)) := by
  rcases v with _ | ⟨b, i⟩
  · exact .refl _
  · fin_cases i
    · have h₁ : seedGraph.Adj seedBase (.inr (.inl (.inl (b, 0)))) := by
        apply seed_vertex_edge_adj
        simp [edgeVertices, circleStart, circleEnd]
      have h₂ : seedGraph.Adj (.inl (.inl (some (b, 0))))
          (.inr (.inl (.inl (b, 0)))) := by
        apply seed_vertex_edge_adj
        simp [edgeVertices, circleStart, circleEnd]
      exact h₁.reachable.trans h₂.reachable.symm
    · have h₁ : seedGraph.Adj seedBase (.inr (.inl (.inl (b, 2)))) := by
        apply seed_vertex_edge_adj
        simp [edgeVertices, circleStart, circleEnd]
      have h₂ : seedGraph.Adj (.inl (.inl (some (b, 1))))
          (.inr (.inl (.inl (b, 2)))) := by
        apply seed_vertex_edge_adj
        simp [edgeVertices, circleStart, circleEnd]
      exact h₁.reachable.trans h₂.reachable.symm

def firstSector (r : Bool) : Sector :=
  ⟨r, ⟨0, by cases r <;> decide⟩⟩

theorem seed_vertex_reachable (v : SeedVertex) :
    seedGraph.Reachable seedBase (.inl v) := by
  rcases v with v | r
  · exact rose_vertex_reachable v
  · let s := firstSector r
    have h₁ : seedGraph.Adj (.inl (.inl (sectorStart s))) (.inr (.inl (.inr s))) := by
      apply seed_vertex_edge_adj
      simp [edgeVertices]
    have h₂ : seedGraph.Adj (.inl (.inr r)) (.inr (.inl (.inr s))) := by
      apply seed_vertex_edge_adj
      simp [edgeVertices, s, firstSector]
    exact ((rose_vertex_reachable (sectorStart s)).trans h₁.reachable).trans h₂.reachable.symm

theorem seed_edge_reachable (e : SeedEdge) :
    seedGraph.Reachable seedBase (.inr (.inl e)) := by
  rcases e with e | s
  · apply (seed_vertex_reachable (.inl (circleStart e))).trans
    apply SimpleGraph.Adj.reachable
    apply seed_vertex_edge_adj
    simp [edgeVertices]
  · apply (seed_vertex_reachable (.inr s.1)).trans
    apply SimpleGraph.Adj.reachable
    apply seed_vertex_edge_adj
    simp [edgeVertices]

theorem seed_cell_reachable (x : SeedCell) : seedGraph.Reachable seedBase x := by
  rcases x with v | e
  · exact seed_vertex_reachable v
  · rcases e with e | s
    · exact seed_edge_reachable e
    · apply (seed_edge_reachable (.inl (sectorCircleEdge s))).trans
      apply SimpleGraph.Adj.reachable
      apply seed_edge_sector_adj
      simp [sectorEdges]

theorem seed_connected : seedGraph.Connected := by
  exact { preconnected := fun v w =>
    (seed_cell_reachable v).symm.trans (seed_cell_reachable w), nonempty := ⟨seedBase⟩ }


end EilenbergGanea

end

end OAI
