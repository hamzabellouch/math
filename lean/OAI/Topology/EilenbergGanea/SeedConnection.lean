import OAI.Topology.EilenbergGanea.SeedHolonomy
import OAI.GroupTheory.RightAngledArtin.Basic

namespace OAI

noncomputable section

open Classical Set Filter Topology MeasureTheory
open scoped Quaternion ContDiff

namespace EilenbergGanea
namespace SeedConnection

def circleWord (e : CircleEdge) : FreeGroup Bool := if e.2 = 0 then FreeGroup.of e.1 else 1

def boundaryEdgeWord (s : Sector) : FreeGroup Bool :=
  if (sectorLetter s).2 then circleWord (sectorCircleEdge s) else
    (circleWord (sectorCircleEdge s))⁻¹

def boundaryWords (r : Bool) : List (FreeGroup Bool) :=
  List.ofFn (fun i : Fin (boundaryLength r) => boundaryEdgeWord ⟨r,i⟩)

theorem boundaryWords_prod : ∀ r, (boundaryWords r).prod = seedRelator r := by
  decide

theorem sector_end : ∀ s : Sector, sectorStart (nextSector s) =
    if (sectorLetter s).2 then circleEnd (sectorCircleEdge s)
    else circleStart (sectorCircleEdge s) := by decide

theorem circle_distinct : ∀ e : CircleEdge, circleStart e ≠ circleEnd e := by decide

theorem sector_distinct : ∀ s : Sector, sectorStart s ≠ sectorStart (nextSector s) := by decide

def circleLabel (e : CircleEdge) : SeedSU2 := FreeGroup.lift seedLetterUnit (circleWord e)

def radialLabel (s : Sector) : SeedSU2 :=
  FreeGroup.lift seedLetterUnit ((boundaryWords s.1).take s.2.val).prod

@[simp] theorem boundaryWords_length (r : Bool) : (boundaryWords r).length = boundaryLength r :=
  List.length_ofFn

@[simp] theorem boundaryWords_get (s : Sector) :
    (boundaryWords s.1)[s.2.val]'(by simp) = boundaryEdgeWord s := by
  simp [boundaryWords]

theorem radial_step (s : Sector) : radialLabel (nextSector s) = radialLabel s *
    (if (sectorLetter s).2 then circleLabel (sectorCircleEdge s)
      else (circleLabel (sectorCircleEdge s))⁻¹) := by
  have hs : s.2.val < (boundaryWords s.1).length := by simp
  have he := congrArg (FreeGroup.lift seedLetterUnit) (congrArg List.prod
    (List.take_succ_eq_append_getElem hs))
  rw [List.prod_append,List.prod_singleton,map_mul,boundaryWords_get] at he
  have hf : FreeGroup.lift seedLetterUnit (boundaryEdgeWord s) =
      if (sectorLetter s).2 then circleLabel (sectorCircleEdge s)
      else (circleLabel (sectorCircleEdge s))⁻¹ := by
    unfold boundaryEdgeWord circleLabel
    split <;> simp
  rw [hf] at he
  change radialLabel (nextSector s) =
    FreeGroup.lift seedLetterUnit ((boundaryWords s.1).take s.2.val).prod * _
  rw [← he]
  unfold radialLabel nextSector
  dsimp only
  by_cases hn : s.2.val + 1 < boundaryLength s.1
  · rw [Nat.mod_eq_of_lt hn]
  · have hn' : s.2.val + 1 = boundaryLength s.1 := by have hh := s.2.isLt; omega
    rw [hn',Nat.mod_self,List.take_zero,List.prod_nil,map_one,
      ← boundaryWords_length,List.take_length,boundaryWords_prod,seedRelator_unit]

def edgeAnchor : SeedEdge → SeedVertex
  | .inl e => .inl (circleStart e)
  | .inr s => .inr s.1

def edgeLocal : SeedEdge → SeedVertex → SeedSU2
  | .inl e, v => if v = .inl (circleStart e) then 1 else circleLabel e
  | .inr s, v => if v = .inr s.1 then 1 else radialLabel s

def faceLocal (s : Sector) (v : SeedVertex) : SeedSU2 :=
  if v = .inr s.1 then 1 else
  if v = .inl (sectorStart s) then radialLabel s else radialLabel (nextSector s)

theorem edgeLocal_anchor (e : SeedEdge) : edgeLocal e (edgeAnchor e) = 1 := by
  cases e <;> simp [edgeLocal,edgeAnchor]

theorem nextSector_first (s : Sector) : (nextSector s).1 = s.1 := rfl

theorem faceLocal_incidence (s : Sector) (e : SeedEdge) (he : e ∈ sectorEdges s)
    (v : SeedVertex) (hv : v ∈ edgeVertices e) :
    faceLocal s v = faceLocal s (edgeAnchor e) * edgeLocal e v := by
  simp only [sectorEdges,Finset.mem_insert,Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl
  · simp only [edgeVertices,Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · simp [edgeAnchor,edgeLocal]
    · have hd := circle_distinct (sectorCircleEdge s)
      have hr := radial_step s
      cases hb : (sectorLetter s).2
      · simp only [hb,Bool.false_eq_true,↓reduceIte] at hr
        simp only [sectorStart,hb,Bool.false_eq_true,↓reduceIte,
          edgeAnchor,edgeLocal,faceLocal,Sum.inl_ne_inr,
          Sum.inl.injEq,Ne.symm hd,hd]
        rw [hr]
        group
      · simp only [hb,↓reduceIte] at hr
        simp only [sectorStart,hb,↓reduceIte,edgeAnchor,edgeLocal,faceLocal,
          Sum.inl_ne_inr,Sum.inl.injEq,Ne.symm hd]
        exact hr
  · simp only [edgeVertices,Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl | rfl <;> simp [faceLocal,edgeLocal,edgeAnchor]
  · simp only [edgeVertices,Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · simp [faceLocal,edgeLocal,edgeAnchor,nextSector_first]
    · simp [faceLocal,edgeLocal,edgeAnchor,nextSector_first,Ne.symm (sector_distinct s)]

def cellRank : SeedCell → ℕ
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr _) => 2

theorem properFace_rank {a b : SeedCell} (h : properFace a b) : cellRank a < cellRank b := by
  rcases a with a | (a | a) <;> rcases b with b | (b | b) <;>
    simp only [properFace,cellRank] at * <;> omega

theorem properFace_trans {a b c : SeedCell} (hab : properFace a b) (hbc : properFace b c) :
    properFace a c := by
  rcases a with a | (a | a) <;> rcases b with b | (b | b) <;>
    rcases c with c | (c | c) <;> simp only [properFace] at *
  exact Finset.mem_biUnion.mpr ⟨b,hbc,hab⟩

def upLabel : SeedCell → SeedCell → SeedSU2
  | .inl v, .inr (.inl e) => (edgeLocal e v)⁻¹
  | .inl v, .inr (.inr s) => (faceLocal s v)⁻¹
  | .inr (.inl e), .inr (.inr s) => (faceLocal s (edgeAnchor e))⁻¹
  | _, _ => 1

@[simp] theorem upLabel_diag (a : SeedCell) : upLabel a a = 1 := by
  rcases a with a | (a | a) <;> rfl

theorem upLabel_same_rank {a b : SeedCell} (hab : cellRank a = cellRank b) :
    upLabel a b = 1 := by
  rcases a with a | (a | a) <;> rcases b with b | (b | b) <;>
    simp [upLabel,cellRank] at *

theorem upLabel_trans {a b c : SeedCell} (hab : a = b ∨ properFace a b)
    (hbc : b = c ∨ properFace b c) : upLabel a b * upLabel b c = upLabel a c := by
  rcases hab with rfl | hab
  · simp
  rcases hbc with rfl | hbc
  · simp
  rcases a with a | (a | a) <;> rcases b with b | (b | b) <;>
    rcases c with c | (c | c) <;> simp only [properFace] at hab hbc
  simp only [upLabel,← mul_inv_rev]
  exact congrArg Inv.inv (faceLocal_incidence c b hbc a hab).symm

def Related (a b : SeedCell) : Prop := a = b ∨ seedGraph.Adj a b

theorem related_symm {a b : SeedCell} : Related a b → Related b a := by
  rintro (rfl | h)
  · exact Or.inl rfl
  · exact Or.inr h.symm

theorem related_forward {a b : SeedCell} (h : Related a b) (hr : cellRank a ≤ cellRank b) :
    a = b ∨ properFace a b := by
  rcases h with h | h
  · exact Or.inl h
  rcases h with h | h
  · exact Or.inr h
  · have hd := properFace_rank h
    omega

def connection (a b : SeedCell) : SeedSU2 :=
  if cellRank a ≤ cellRank b then upLabel a b else (upLabel b a)⁻¹

@[simp] theorem connection_diag (a : SeedCell) : connection a a = 1 := by
  simp [connection]

theorem connection_reverse (a b : SeedCell) : connection b a = (connection a b)⁻¹ := by
  by_cases hab : cellRank a ≤ cellRank b
  · by_cases hba : cellRank b ≤ cellRank a
    · have he := le_antisymm hab hba
      simp [connection,hab,hba,upLabel_same_rank he,upLabel_same_rank he.symm]
    · simp [connection,hab,hba]
  · have hba : cellRank b ≤ cellRank a := (le_total _ _).resolve_left hab
    simp [connection,hab,hba]

theorem connection_flat_sorted {a b c : SeedCell} (hab : Related a b) (hbc : Related b c)
    (hrab : cellRank a ≤ cellRank b) (hrbc : cellRank b ≤ cellRank c) :
    connection a b * connection b c = connection a c := by
  simp only [connection,hrab,hrbc,le_trans hrab hrbc,↓reduceIte]
  exact upLabel_trans (related_forward hab hrab) (related_forward hbc hrbc)

theorem connection_flat {a b c : SeedCell} (hab : Related a b) (hbc : Related b c)
    (hac : Related a c) : connection a b * connection b c = connection a c := by
  by_cases hrab : cellRank a ≤ cellRank b
  · by_cases hrbc : cellRank b ≤ cellRank c
    · exact connection_flat_sorted hab hbc hrab hrbc
    · have hrcb := le_of_lt (lt_of_not_ge hrbc)
      by_cases hrac : cellRank a ≤ cellRank c
      · have H := connection_flat_sorted hac (related_symm hbc) hrac hrcb
        rw [connection_reverse b c] at H
        rw [← H]
        group
      · have hrca := le_of_lt (lt_of_not_ge hrac)
        have H := connection_flat_sorted (related_symm hac) hab hrca hrab
        rw [connection_reverse a c,connection_reverse b c] at H
        calc
          connection a b * connection b c =
              connection a c * ((connection a c)⁻¹ * connection a b) * connection b c := by group
          _ = connection a c * (connection b c)⁻¹ * connection b c := by rw [H]
          _ = connection a c := by group
  · have hrba := le_of_lt (lt_of_not_ge hrab)
    by_cases hrac : cellRank a ≤ cellRank c
    · have H := connection_flat_sorted (related_symm hab) hac hrba hrac
      rw [connection_reverse a b] at H
      rw [← H]
      group
    · have hrca := le_of_lt (lt_of_not_ge hrac)
      by_cases hrbc : cellRank b ≤ cellRank c
      · have H := connection_flat_sorted hbc (related_symm hac) hrbc hrca
        rw [connection_reverse a c,connection_reverse a b] at H
        calc
          connection a b * connection b c =
              connection a b * (connection b c * (connection a c)⁻¹) * connection a c := by group
          _ = connection a b * (connection a b)⁻¹ * connection a c := by rw [H]
          _ = connection a c := by group
      · have hrcb := le_of_lt (lt_of_not_ge hrbc)
        have H := connection_flat_sorted (related_symm hbc) (related_symm hab) hrcb hrba
        rw [connection_reverse b c,connection_reverse a b,connection_reverse a c] at H
        have H' := congrArg Inv.inv H
        simpa only [mul_inv_rev,inv_inv] using H'

def rankFin (a : SeedCell) : Fin 3 := ⟨cellRank a,by
  rcases a with a | (a | a) <;> norm_num [cellRank]⟩

theorem adjacent_rank_ne {a b : SeedCell} (h : seedGraph.Adj a b) : rankFin a ≠ rankFin b := by
  intro he
  have he' := congrArg Fin.val he
  change cellRank a = cellRank b at he'
  rcases h with h | h <;> have hh := properFace_rank h <;> omega

theorem clique_card_le_three (s : Finset SeedCell) (hs : (s : Set SeedCell).Pairwise seedGraph.Adj) :
    s.card ≤ 3 := by
  have hi : Set.InjOn rankFin (s : Set SeedCell) := by
    intro a ha b hb he
    by_contra hn
    exact adjacent_rank_ne (hs ha hb hn) he
  have hc := Finset.card_le_card (Finset.subset_univ (s.image rankFin))
  rwa [Finset.card_image_of_injOn hi,Finset.card_univ,Fintype.card_fin] at hc

/-- The subdivided x-circle in the exact 103-cell order graph. -/
def roseLoop : List SeedCell :=
  [.inl (.inl none), .inr (.inl (.inl (false,0))),
    .inl (.inl (some (false,0))), .inr (.inl (.inl (false,1))),
    .inl (.inl (some (false,1))), .inr (.inl (.inl (false,2))), .inl (.inl none)]

theorem roseLoop_edges : roseLoop.IsChain seedGraph.Adj := by
  simp [roseLoop,List.isChain_cons_cons,seedGraph,properFace,edgeVertices,circleStart,circleEnd]

theorem roseLoop_holonomy : (List.zipWith connection roseLoop roseLoop.tail).prod = seedXUnit := by
  simp [roseLoop,connection,cellRank,upLabel,edgeLocal,circleLabel,circleWord,
    circleStart,seedLetterUnit]

theorem roseLoop_nontrivial : (List.zipWith connection roseLoop roseLoop.tail).prod ≠ 1 := by
  rw [roseLoop_holonomy]
  intro h
  have hh := congrArg (fun q : SeedSU2 => (q : ℍ).re) h
  norm_num [seedXUnit,seedXQuaternion] at hh

end SeedConnection



end EilenbergGanea

end

end OAI
