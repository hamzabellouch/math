import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Balance.WordPackingPieri
import OAI.RepresentationTheory.UniversalSquare.Balance.EmptyPacking
import OAI.RepresentationTheory.UniversalSquare.Specht.ThreeRowMasks

namespace OAI

/-! Packing Plans. -/

section

noncomputable section
namespace Saxl.Balance
open Columns FlagColumns

inductive PackingPlan where
  | empty
  | neighbor (r : ℕ) (parts : List ℕ)
  | repeated (m k : ℕ)
  | twosOdd (m x : ℕ) (parts : List ℕ)
  | twoPaths (q : ℕ) (parts : List ℕ)
  | threeRows (m s : ℕ) (parts : List ℕ) (strips : List UniversalTensorSquare.ThreeRowEntry)
  | join (p q : PackingPlan)
  deriving DecidableEq

namespace PackingPlan

def columns : PackingPlan → List ℕ
  | .empty => []
  | .neighbor r _ => [r+1,r]
  | .repeated m k => List.replicate m k
  | .twosOdd m x _ => List.replicate m 2 ++ [x]
  | .twoPaths q _ => [q+2,q] ++ List.replicate 2 1
  | .threeRows m s _ _ => ThreeRow.columns m s
  | .join p q => p.columns ++ q.columns

def parts : PackingPlan → List ℕ
  | .empty => []
  | .neighbor _ ps => ps
  | .repeated m k => [m*k]
  | .twosOdd _ _ ps => ps
  | .twoPaths _ ps => ps
  | .threeRows _ _ ps _ => ps
  | .join p q => p.parts ++ q.parts

def bands : PackingPlan → List (ℕ × ℕ)
  | .empty => []
  | .neighbor r _ => [(r,r+1)]
  | .repeated _ k => [(k,k)]
  | .twosOdd _ x _ => [(2,2),(x,x)]
  | .twoPaths q _ => [(q,2*q+3),(1,1)]
  | .threeRows _ _ _ _ => [(1,3)]
  | .join p q => p.bands ++ q.bands

def marks (p : PackingPlan) : Finset ℕ := bandStarts p.bands

def Valid : PackingPlan → ℕ → Prop
  | .empty,_ => True
  | .neighbor r ps,d => 0 < r ∧ r+1 ≤ d ∧ ps.sum = 2*r+1 ∧ ps.length ≤ 4
  | .repeated m k,d => 0 < m ∧ 0 < k ∧ k ≤ d
  | .twosOdd m x ps,d => 1 ≤ m ∧ Odd x ∧ x ≤ 2*m ∧ 2 ≤ d ∧ x ≤ d ∧
      ps.sum = 2*m+x ∧ ps.length ≤ 2
  | .twoPaths q ps,d => 3 ≤ q ∧ q+2 ≤ d ∧ ps.sum = 2*q+4 ∧ ps.length ≤ 4
  | .threeRows m s ps cs,d => 3 ≤ d ∧ UniversalTensorSquare.ThreeRowMask m s ps cs
  | .join p q,d => p.Valid d ∧ q.Valid d ∧ Disjoint p.marks q.marks

instance (p : PackingPlan) (d : ℕ) : Decidable (p.Valid d) := by
  induction p with
  | empty => exact isTrue True.intro
  | neighbor r ps => unfold Valid; infer_instance
  | repeated m k => unfold Valid; infer_instance
  | twosOdd m x ps => unfold Valid; infer_instance
  | twoPaths q ps => unfold Valid; infer_instance
  | threeRows m s ps cs => unfold Valid; infer_instance
  | join p q ip iq => unfold Valid; infer_instance

theorem realize (p : PackingPlan) {d : ℕ} (h : p.Valid d)
    (A : Fin (d*d) → Prop) (label : Fin (d*d) → ℕ)
    (he : ∀ e ∈ p.bands, ∀ z, (A z ∧ label z = e.1) ↔ output z ∈ Set.Icc e.1 e.2) :
    Nonempty (WordPacking p.columns p.parts d A label p.marks) := by
  induction p with
  | empty => simpa [columns,parts,marks,bands,bandStarts] using
      Nonempty.intro (WordPacking.empty d A label)
  | neighbor r ps =>
    rcases h with ⟨hr,hd,hs,hl⟩
    simpa [columns,parts,marks,bands,bandStarts] using
      WordPacking.neighbor hr hd hs hl r A label (he (r,r+1) (by simp [bands]))
  | repeated m k =>
    rcases h with ⟨hm,hk,hd⟩
    have hei : ∀ z, (A z ∧ label z = k) ↔ output z = k := by
      intro z
      rw [he (k,k) (by simp [bands]) z]
      simp only [Set.mem_Icc]; omega
    simpa [columns,parts,marks,bands,bandStarts] using WordPacking.repeated hm hk hd k A label hei
  | twosOdd m x ps =>
    rcases h with ⟨hm,hx,hxc,hd,hd',hs,hl⟩
    have hne : 2 ≠ x := by intro heq; rw [← heq] at hx; norm_num at hx
    have hei : ∀ k, (k,k) ∈ (PackingPlan.twosOdd m x ps).bands →
        ∀ z, (A z ∧ label z = k) ↔ output z = k := by
      intro k hk z
      rw [he (k,k) hk z]
      simp only [Set.mem_Icc]; omega
    simpa [columns,parts,marks,bands,bandStarts] using WordPacking.twosOdd hm hx hxc hd hd' hs hl
      2 x hne A label (hei 2 (by simp [bands])) (hei x (by simp [bands]))
  | twoPaths q ps =>
    rcases h with ⟨hq,hd,hs,hl⟩
    have he1 : ∀ z, (A z ∧ label z = 1) ↔ output z = 1 := by
      intro z
      rw [he (1,1) (by simp [bands]) z]
      simp only [Set.mem_Icc]; omega
    simpa [columns,parts,marks,bands,bandStarts] using WordPacking.twoPaths hq hd hs hl
      q 1 (by omega) A label (he (q,2*q+3) (by simp [bands])) he1
  | threeRows m s ps cs =>
    simpa [columns,parts,marks,bands,bandStarts] using
      WordPacking.threeRows h.1 h.2 A label (he (1,3) (by simp [bands]))
  | join p q ip iq =>
    obtain ⟨P⟩ := ip h.1 (by intro e he' z; exact he e (List.mem_append_left _ he') z)
    obtain ⟨Q⟩ := iq h.2.1 (by intro e he' z; exact he e (List.mem_append_right _ he') z)
    simpa only [columns,parts,marks,bands,bandStarts,List.map_append,List.toFinset_append] using
      Nonempty.intro (P.join Q h.2.2)

end PackingPlan
end Saxl.Balance

namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns Saxl.FlagColumns

theorem packingPlan_pos {n d : ℕ} (p : PackingPlan) {lam μ : YoungDiagram}
    (hv : p.Valid d) (hb : BandsValid p.bands) (hheight : lam.colLen 0 = d)
    (hc : p.columns.Perm lam.transpose.rowLens) (hp : ∀ x ∈ p.parts, 0 < x)
    (a : Tableau n lam) (t : Tableau n μ)
    (hd : Dominates μ (columnShape p.parts).transpose) : 0 < kronecker a a t := by
  obtain ⟨e,hr,hc'⟩ := place_columns lam hc
  have hn : p.columns.sum = n := by
    simpa only [Fintype.card_fin] using Fintype.card_congr (((enumerate p.columns).trans e).trans a.symm)
  subst n
  let B := numericBands p.bands hb
  obtain ⟨P⟩ := p.realize hv (B.alphabet d) (B.letterLabel d)
    (fun e he z => numericBands_iff hb he z)
  rw [← hheight] at P
  let a' := (enumerate p.columns).trans e
  exact kronecker_pos_of_shapes rfl rfl rfl a' a' t a a t
    (P.kronecker_pos a' t (standard_placed_self e hr hc') hp (B.letter_ordered _) hd)

end UniversalTensorSquare
end
end

end OAI
