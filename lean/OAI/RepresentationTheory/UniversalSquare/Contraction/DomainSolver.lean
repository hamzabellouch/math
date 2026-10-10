import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Contraction.DomainContractions

namespace OAI

/-! Domain Solver. -/

section

open scoped BigOperators
namespace Saxl.Columns

def edgeOptions {rsT rsA rsB : List ℕ}
    (D : Domains rsT) (E : Domains rsA) (F : Domains rsB)
    (c : Edge rsT rsA rsB) (flag : Finset (ℕ × ℕ × ℕ)) : Finset (ℕ × ℕ × ℕ) :=
  flag.filter (fun v => (D.atValue c.1 v.1).vanished = false ∧
    (E.atValue c.2.1 v.2.1).vanished = false ∧ (F.atValue c.2.2 v.2.2).vanished = false)

lemma domainContraction_cons_options {rsT rsA rsB : List ℕ}
    (D : Domains rsT) (E : Domains rsA) (F : Domains rsB)
    (c : Edge rsT rsA rsB) (edges : List (Edge rsT rsA rsB))
    (flag : Finset (ℕ × ℕ × ℕ)) :
    domainContraction D E F (c::edges) flag =
      ∑ v ∈ edgeOptions D E F c flag, domainContraction (D.atValue c.1 v.1)
        (E.atValue c.2.1 v.2.1) (F.atValue c.2.2 v.2.2) edges flag := by
  rw [domainContraction_cons, edgeOptions, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v hv
  split_ifs with h
  · rfl
  · apply domainContraction_zero
    simpa only [Bool.or_eq_true, Bool.not_eq_false, not_and_or, or_assoc] using h

def bringBest {α : Type*} (score : α → ℕ) : List α → List α
  | [] => []
  | c :: cs => match bringBest score cs with
    | [] => [c]
    | d :: ds => if score c ≤ score d then c :: d :: ds else d :: c :: ds

lemma bringBest_perm {α : Type*} (score : α → ℕ) (cs : List α) :
    (bringBest score cs).Perm cs := by
  induction cs with
  | nil => exact List.Perm.refl _
  | cons c cs ih =>
    rw [bringBest]
    cases he : bringBest score cs with
    | nil =>
      rw [he] at ih
      exact List.Perm.cons c ih
    | cons d ds =>
      rw [he] at ih
      simp only
      split_ifs
      · exact List.Perm.cons c ih
      · exact (List.Perm.swap _ _ _).trans (List.Perm.cons c ih)

def orderEdges {rsT rsA rsB : List ℕ}
    (D : Domains rsT) (E : Domains rsA) (F : Domains rsB)
    (edges : List (Edge rsT rsA rsB)) (flag : Finset (ℕ × ℕ × ℕ)) : List (Edge rsT rsA rsB) :=
  bringBest (fun c => (edgeOptions D E F c flag).card) edges

lemma orderEdges_perm {rsT rsA rsB : List ℕ}
    (D : Domains rsT) (E : Domains rsA) (F : Domains rsB)
    (edges : List (Edge rsT rsA rsB)) (flag : Finset (ℕ × ℕ × ℕ)) :
    (orderEdges D E F edges flag).Perm edges := bringBest_perm _ _

def solveDomains {rsT rsA rsB : List ℕ} : ℕ → Domains rsT → Domains rsA → Domains rsB →
    List (Edge rsT rsA rsB) → Finset (ℕ × ℕ × ℕ) → ℤ
  | fuel, D, E, F, edges, flag =>
    if D.vanished || E.vanished || F.vanished then 0
    else match orderEdges D E F edges flag with
      | [] => D.mass * E.mass * F.mass
      | c :: cs => match fuel with
        | 0 => 0
        | k+1 => ∑ v ∈ edgeOptions D E F c flag,
          solveDomains k (D.atValue c.1 v.1) (E.atValue c.2.1 v.2.1)
            (F.atValue c.2.2 v.2.2) cs flag

theorem solveDomains_correct {rsT rsA rsB : List ℕ} (fuel : ℕ)
    (D : Domains rsT) (E : Domains rsA) (F : Domains rsB)
    (edges : List (Edge rsT rsA rsB)) (flag : Finset (ℕ × ℕ × ℕ))
    (h : edges.length ≤ fuel) :
    solveDomains fuel D E F edges flag = domainContraction D E F edges flag := by
  induction fuel generalizing D E F edges with
  | zero =>
    have hh : orderEdges D E F edges flag = [] := by
      apply List.length_eq_zero_iff.mp
      rw [(orderEdges_perm D E F edges flag).length_eq]
      omega
    rw [solveDomains]
    split_ifs with hv
    · exact (domainContraction_zero D E F edges flag hv).symm
    · rw [hh]
      rw [← domainContraction_perm D E F (orderEdges_perm D E F edges flag) flag, hh]
      exact (domainContraction_nil D E F flag).symm
  | succ fuel ih =>
    rw [solveDomains]
    split_ifs with hv
    · exact (domainContraction_zero D E F edges flag hv).symm
    · have hp := orderEdges_perm D E F edges flag
      rw [← domainContraction_perm D E F hp flag]
      cases he : orderEdges D E F edges flag with
      | nil => exact (domainContraction_nil D E F flag).symm
      | cons c cs =>
        have hlen : cs.length ≤ fuel := by
          have hl := hp.length_eq
          rw [he, List.length_cons] at hl
          omega
        rw [domainContraction_cons_options]
        apply Finset.sum_congr rfl
        intro v hv
        exact ih _ _ _ _ hlen

def certificateEdges {n : ℕ} (rsA rsB rsT : List ℕ)
    (ea : Fin n ≃ Fin rsA.sum) (eb : Fin n ≃ Fin rsB.sum) (et : Fin n ≃ Fin rsT.sum) :
    List (Edge rsT rsA rsB) :=
  List.ofFn (fun i => (enumerate rsT (et i), enumerate rsA (ea i), enumerate rsB (eb i)))

lemma contractionInteger_domains {n : ℕ} (rsA rsB rsT : List ℕ)
    (ea : Fin n ≃ Fin rsA.sum) (eb : Fin n ≃ Fin rsB.sum) (et : Fin n ≃ Fin rsT.sum)
    (flag : Finset (ℕ × ℕ × ℕ)) :
    contractionInteger rsA rsB rsT ea eb et (fun r a b => if (r,a,b) ∈ flag then 1 else 0) =
      domainContraction (.full rsT) (.full rsA) (.full rsB)
        (certificateEdges rsA rsB rsT ea eb et) flag := by
  simp only [contractionInteger, domainContraction, Domains.full_weight,
    certificateEdges, List.map_ofFn, List.prod_ofFn, Function.comp_apply]

theorem contractionInteger_solve {n : ℕ} (rsA rsB rsT : List ℕ)
    (ea : Fin n ≃ Fin rsA.sum) (eb : Fin n ≃ Fin rsB.sum) (et : Fin n ≃ Fin rsT.sum)
    (flag : Finset (ℕ × ℕ × ℕ)) :
    contractionInteger rsA rsB rsT ea eb et (fun r a b => if (r,a,b) ∈ flag then 1 else 0) =
      solveDomains n (.full rsT) (.full rsA) (.full rsB)
        (certificateEdges rsA rsB rsT ea eb et) flag := by
  rw [solveDomains_correct n _ _ _ _ _ (by simp [certificateEdges])]
  exact contractionInteger_domains ..

end Saxl.Columns
end

end OAI
