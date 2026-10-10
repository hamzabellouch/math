import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.GroupTheory.GroupAction.Basic

namespace OAI

/-! Basic data for actions on simplicial trees. -/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
variable {G V : Type} [Group G] [MulAction G V]
variable (T : SimpleGraph V)

def PreservesAdj : Prop := ∀ g : G, ∀ {u v : V}, T.Adj u v → T.Adj (g • u) (g • v)

def translate (hA : PreservesAdj (G := G) T) (g : G) : T →g T :=
  ⟨(g • ·),hA g⟩

def pairStabilizer (u v : V) : Subgroup G :=
  MulAction.stabilizer G u ⊓ MulAction.stabilizer G v

/-- A set contains the unique path between any two of its vertices. -/
def PathClosed (T : SimpleGraph V) (U : Set V) : Prop :=
  ∀ ⦃u v⦄, u∈U → v∈U → ∀ p : T.Walk u v, p.IsPath → ∀ w∈p.support,w∈U

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
