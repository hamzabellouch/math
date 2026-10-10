import Mathlib
import OAI.SetTheory.PartitionConsistency.Logic.Proofs

namespace OAI

namespace PartitionConsistency
namespace SetLanguage
open Formula

/-! All abbreviations in this namespace expand to formulas of the pure language
of equality and membership. Functions are sets of Kuratowski pairs *inside the
structure*. In particular, no quantification over external Lean functions is
used in PP, Choice, or ordinal-indexed Choice. -/

/-- `a ⊆ b`. -/
def subset {n} (a b : Fin n) : Formula n :=
  rename ![a, b] (Formula.all ((Formula.mem 2 0).imp (Formula.mem 2 1)) : Formula 2)

/-- `a = ∅`. -/
def empty {n} (a : Fin n) : Formula n :=
  rename ![a] (Formula.all (Formula.mem 1 0).neg : Formula 1)

/-- `a ≠ ∅`, stated as existence of a member. -/
def nonempty {n} (a : Fin n) : Formula n :=
  rename ![a] (Formula.ex (Formula.mem 1 0) : Formula 1)

/-- `p = {x,y}`. -/
def unorderedPair {n} (p x y : Fin n) : Formula n :=
  rename ![p, x, y]
    (Formula.all ((Formula.mem 3 0).iff ((Formula.equal 3 1).disj (Formula.equal 3 2))) : Formula 3)

/-- `b = a ∪ {a}`. -/
def successor {n} (b a : Fin n) : Formula n :=
  rename ![b, a]
    (Formula.all ((Formula.mem 2 0).iff ((Formula.mem 2 1).disj (Formula.equal 2 1))) : Formula 2)

/-- Kuratowski ordered pair: `p = {{x},{x,y}}`. -/
def orderedPair {n} (p x y : Fin n) : Formula n :=
  rename ![p, x, y]
    (Formula.ex (Formula.ex ((unorderedPair 3 1 1).conj
      ((unorderedPair 4 1 2).conj (unorderedPair 0 3 4)))) : Formula 3)

/-- The internal graph relation `⟨x,y⟩ ∈ f`. -/
def edge {n} (f x y : Fin n) : Formula n :=
  rename ![f, x, y]
    (Formula.ex ((Formula.mem 3 0).conj (orderedPair 3 1 2)) : Formula 3)

/-- `f` is a set graph of a function whose domain is exactly `d`.
The first conjunct excludes non-pairs and graph entries outside the domain;
the second conjunct asserts totality and single-valuedness. -/
def functionOn {n} (f d : Fin n) : Formula n :=
  rename ![f, d]
    ((Formula.all ((Formula.mem 2 0).imp
        (Formula.ex (Formula.ex ((Formula.mem 3 1).conj (orderedPair 2 3 4)))))).conj
      (Formula.all ((Formula.mem 2 1).imp
        (Formula.ex ((edge 0 2 3).conj (Formula.all ((edge 0 2 4).imp (Formula.equal 4 3))))))) : Formula 2)

/-- Internal set function `f : d → r`. -/
def mapsTo {n} (f d r : Fin n) : Formula n :=
  rename ![f, d, r]
    ((functionOn 0 1).conj
      (Formula.all (Formula.all ((Formula.mem 3 1).imp ((edge 0 3 4).imp (Formula.mem 4 2))))) : Formula 3)

/-- Internal set surjection `f : d ↠ r`. -/
def surjection {n} (f d r : Fin n) : Formula n :=
  rename ![f, d, r]
    ((mapsTo 0 1 2).conj
      (Formula.all ((Formula.mem 3 2).imp (Formula.ex ((Formula.mem 4 1).conj (edge 0 4 3))))) : Formula 3)

/-- Internal set injection `f : d ↪ r`. -/
def injection {n} (f d r : Fin n) : Formula n :=
  rename ![f, d, r]
    ((mapsTo 0 1 2).conj
      (Formula.all (Formula.all (.all
        ((Formula.mem 3 1).imp ((Formula.mem 4 1).imp
          (((edge 0 3 5).conj (edge 0 4 5)).imp (Formula.equal 3 4))))))) : Formula 3)

/-- Transitivity of a set (not transitivity of the external structure). -/
def transitiveSet {n} (a : Fin n) : Formula n :=
  rename ![a]
    (Formula.all (Formula.all ((Formula.mem 1 0).imp ((Formula.mem 2 1).imp (Formula.mem 2 0)))) : Formula 1)

/-- Membership is an internal strict linear order on `a`. -/
def membershipLinear {n} (a : Fin n) : Formula n :=
  rename ![a]
    ((Formula.all ((Formula.mem 1 0).imp (Formula.mem 1 1).neg)).conj
      ((Formula.all (Formula.all (Formula.all ((Formula.mem 1 0).imp ((Formula.mem 2 0).imp ((Formula.mem 3 0).imp
        (((Formula.mem 1 2).conj (Formula.mem 2 3)).imp (Formula.mem 1 3)))))))).conj
        (Formula.all (Formula.all ((Formula.mem 1 0).imp ((Formula.mem 2 0).imp
          ((Formula.equal 1 2).disj ((Formula.mem 1 2).disj (Formula.mem 2 1)))))))) : Formula 1)

/-- Every nonempty internal subset of `a` has a membership-minimal element.
This does NOT assert external well-foundedness of the relation. -/
def membershipWellFounded {n} (a : Fin n) : Formula n :=
  rename ![a]
    (Formula.all (((subset 1 0).conj (nonempty 1)).imp
      (Formula.ex ((Formula.mem 2 1).conj (Formula.all ((Formula.mem 3 1).imp (Formula.mem 3 2).neg))))) : Formula 1)

/-- A von Neumann ordinal: a transitive set internally wellordered by membership. -/
def ordinal {n} (a : Fin n) : Formula n :=
  (transitiveSet a).conj ((membershipLinear a).conj (membershipWellFounded a))

/-- A choice function on the set `A` of nonempty sets. -/
def choiceOn {n} (c A : Fin n) : Formula n :=
  rename ![c, A]
    ((functionOn 0 1).conj
      (Formula.all ((Formula.mem 2 1).imp (Formula.ex ((edge 0 2 3).conj (Formula.mem 3 2))))) : Formula 2)

/-- A graph `F` coding a family of nonempty sets indexed by ordinal `η`. -/
def nonemptyFamily {n} (F η : Fin n) : Formula n :=
  rename ![F, η]
    ((functionOn 0 1).conj
      (Formula.all (Formula.all ((Formula.mem 2 1).imp ((edge 0 2 3).imp (nonempty 3))))) : Formula 2)

/-- `c(ξ) ∈ F(ξ)` for every `ξ ∈ η`, with `c` an internal function. -/
def choiceForFamily {n} (c η F : Fin n) : Formula n :=
  rename ![c, η, F]
    ((functionOn 0 1).conj
      (Formula.all (Formula.all ((Formula.mem 3 1).imp ((edge 2 3 4).imp
        (Formula.ex ((edge 0 3 5).conj (Formula.mem 5 4))))))) : Formula 3)

/-- The Partition Principle. The reverse injection is not required to be a
section of the original surjection. Both `X` and `Y` range over all sets. -/
def PP : Sentence :=
  Formula.all (Formula.all ((Formula.ex (surjection 2 0 1)).imp (Formula.ex (injection 2 1 0))))

/-- Ordinary Choice for every set of nonempty sets. -/
def AC : Sentence :=
  Formula.all ((Formula.all ((Formula.mem 1 0).imp (nonempty 1))).imp (Formula.ex (choiceOn 1 0)))

/-- Choice for every ordinal-indexed family of nonempty sets, including ordinals
which may fail to be well founded from outside a model. -/
def ACwo : Sentence :=
  Formula.all ((ordinal 0).imp
    (Formula.all ((nonemptyFamily 1 0).imp (Formula.ex (choiceForFamily 2 0 1)))))

/-! Full pure-set ZF, not a finite fragment and not ZFA. -/

def extensionality : Sentence :=
  Formula.all (Formula.all ((Formula.all ((Formula.mem 2 0).iff (Formula.mem 2 1))).imp (Formula.equal 0 1)))

def emptySet : Sentence := Formula.ex (empty 0)

def pairing : Sentence := Formula.all (Formula.all (Formula.ex (unorderedPair 2 0 1)))

def union : Sentence :=
  Formula.all (Formula.ex (Formula.all ((Formula.mem 2 1).iff (Formula.ex ((Formula.mem 3 0).conj (Formula.mem 2 3))))))

def powerSet : Sentence := Formula.all (Formula.ex (Formula.all ((Formula.mem 2 1).iff (subset 2 0))))

def infinity : Sentence :=
  Formula.ex ((Formula.ex ((Formula.mem 1 0).conj (empty 1))).conj
    (Formula.all ((Formula.mem 1 0).imp (Formula.ex ((Formula.mem 2 0).conj (successor 2 1))))))

def foundation : Sentence :=
  Formula.all ((nonempty 0).imp
    (Formula.ex ((Formula.mem 1 0).conj (Formula.all ((Formula.mem 2 1).imp (Formula.mem 2 0).neg)))))

/-- The instance of Separation for an entirely arbitrary formula `p(params,x)`.
All parameters are universally closed. Neither the quantifier complexity of
`p` nor the number of parameters is bounded. -/
def separation {n} (p : Formula (n + 1)) : Sentence :=
  let A : Fin (n + 3) := (Fin.last n).castSucc.castSucc
  let B : Fin (n + 3) := (Fin.last (n + 1)).castSucc
  let x : Fin (n + 3) := Fin.last (n + 2)
  let r : Fin (n + 1) → Fin (n + 3) :=
    Fin.lastCases x (fun i => i.castSucc.castSucc.castSucc)
  close (Formula.all (Formula.ex (Formula.all ((Formula.mem x B).iff ((Formula.mem x A).conj (rename r p))))))

/-- Substitution into a binary formula with `n` additional parameters. -/
def relation {n m} (p : Formula (n + 2)) (params : Fin n → Fin m) (x y : Fin m) :
    Formula m :=
  rename (Fin.lastCases y (Fin.lastCases x params)) p

/-- The instance of Replacement for an entirely arbitrary formula
`p(params,x,y)`: if it is single-valued and total on `A`, its image is a set.
As with Separation, the parameters are all universally closed. -/
def replacement {n} (p : Formula (n + 2)) : Sentence :=
  let unique : Formula (n + 3) :=
    Formula.all ((relation p (fun i => i.castSucc.castSucc.castSucc.castSucc)
      (Fin.last (n + 1)).castSucc.castSucc (Fin.last (n + 3))).imp
      (Formula.equal (Fin.last (n + 3)) (Fin.last (n + 2)).castSucc))
  let totalFunctional : Formula (n + 1) :=
    Formula.all ((Formula.mem (Fin.last (n + 1)) (Fin.last n).castSucc).imp
      (Formula.ex ((relation p (fun i => i.castSucc.castSucc.castSucc)
        (Fin.last (n + 1)).castSucc (Fin.last (n + 2))).conj unique)))
  let image : Formula (n + 1) :=
    Formula.ex (Formula.all ((Formula.mem (Fin.last (n + 2)) (Fin.last (n + 1)).castSucc).iff
      (Formula.ex ((Formula.mem (Fin.last (n + 3)) (Fin.last n).castSucc.castSucc.castSucc).conj
        (relation p (fun i => i.castSucc.castSucc.castSucc.castSucc)
          (Fin.last (n + 3)) (Fin.last (n + 2)).castSucc)))))
  close (Formula.all (totalFunctional.imp image))

/-- Exactly the axioms and all schema instances of pure first-order ZF. -/
inductive IsZFAxiom : Sentence → Prop where
  | extensionality : IsZFAxiom extensionality
  | emptySet : IsZFAxiom emptySet
  | pairing : IsZFAxiom pairing
  | union : IsZFAxiom union
  | powerSet : IsZFAxiom powerSet
  | infinity : IsZFAxiom infinity
  | foundation : IsZFAxiom foundation
  | separation {n} (p : Formula (n + 1)) : IsZFAxiom (separation p)
  | replacement {n} (p : Formula (n + 2)) : IsZFAxiom (replacement p)

/-- Zermelo–Fraenkel set theory, without Choice. -/
def ZF : Theory := {p | IsZFAxiom p}

/-- The exact theory in target `thm:main-consistency`. -/
def targetTheory : Theory := ZF ∪ {PP, ACwo, AC.neg}

end SetLanguage
end PartitionConsistency

end OAI
