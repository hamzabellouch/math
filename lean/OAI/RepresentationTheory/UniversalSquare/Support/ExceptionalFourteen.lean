import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Balance.ExceptionalPacking

namespace OAI

/-! Exceptional Fourteen. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance

def exceptionalPlan71 : PackingPlan := (.join (.neighbor 13 [7,7,7,6]) (.join (.neighbor 7 [4,4,4,3]) (.join (.neighbor 5 [3,3,3,2]) (.join (.neighbor 3 [2,2,2,1]) (.twosOdd 5 1 [6,5])))))

def exceptionalRows71 : List ℕ := [7,7,7,6,6,5,4,4,4,3,3,3,3,2,2,2,2,1]

lemma exceptionalCheck71 : ∀ d ∈ List.range 4, ∀ e ∈ List.range 4,
    ∀ a ∈ List.range exceptionalRows71.length, ∀ c ∈ List.range exceptionalRows71.length,
      refinedCheck 71 10 8 (d+1) (e+1) (a+1) (c+1) exceptionalRows71 := by
  decide +kernel

lemma exceptionalCard71 : (candidate 10 4 0).card = 71 := by
  rw [candidate_card _ _ _ (by decide), staircase_card]

lemma exceptional_pos71 (μ : YoungDiagram) (hμ : μ.card = 71) :
    0 < kronecker (canonicalTableau (candidate 10 4 0) exceptionalCard71)
      (canonicalTableau (candidate 10 4 0) exceptionalCard71) (canonicalTableau μ hμ) := by
  apply candidate_refined_pos (r := 8) (by decide) (by decide) (by decide) rfl
    (by decide) exceptionalCard71 exceptionalRows71 (by decide) (by decide) rfl
    exceptionalPlan71 (by decide) (by decide) (by decide) (by decide) exceptionalCheck71 μ hμ

def exceptionalPlan73 : PackingPlan := (.join (.twoPaths 13 [8,8,7,7]) (.join (.neighbor 7 [4,4,4,3]) (.join (.neighbor 5 [3,3,3,2]) (.join (.repeated 1 4) (.twosOdd 5 3 [7,6])))))

def exceptionalRows73 : List ℕ := [8,8,7,7,7,6,4,4,4,4,3,3,3,3,2]

lemma exceptionalCheck73 : ∀ d ∈ List.range 4, ∀ e ∈ List.range 4,
    ∀ a ∈ List.range exceptionalRows73.length, ∀ c ∈ List.range exceptionalRows73.length,
      refinedCheck 73 10 9 (d+1) (e+1) (a+1) (c+1) exceptionalRows73 := by
  decide +kernel

lemma exceptionalCard73 : (candidate 10 4 1).card = 73 := by
  rw [candidate_card _ _ _ (by decide), staircase_card]

lemma exceptional_pos73 (μ : YoungDiagram) (hμ : μ.card = 73) :
    0 < kronecker (canonicalTableau (candidate 10 4 1) exceptionalCard73)
      (canonicalTableau (candidate 10 4 1) exceptionalCard73) (canonicalTableau μ hμ) := by
  apply candidate_refined_pos (r := 9) (by decide) (by decide) (by decide) rfl
    (by decide) exceptionalCard73 exceptionalRows73 (by decide) (by decide) rfl
    exceptionalPlan73 (by decide) (by decide) (by decide) (by decide) exceptionalCheck73 μ hμ

def exceptionalPlan75 : PackingPlan := (.join (.neighbor 14 [8,7,7,7]) (.join (.neighbor 7 [4,4,4,3]) (.join (.neighbor 5 [3,3,3,2]) (.join (.neighbor 3 [2,2,2,1]) (.twosOdd 6 1 [7,6])))))

def exceptionalRows75 : List ℕ := [8,7,7,7,7,6,4,4,4,3,3,3,3,2,2,2,2,1]

lemma exceptionalCheck75 : ∀ d ∈ List.range 4, ∀ e ∈ List.range 4,
    ∀ a ∈ List.range exceptionalRows75.length, ∀ c ∈ List.range exceptionalRows75.length,
      refinedCheck 75 10 10 (d+1) (e+1) (a+1) (c+1) exceptionalRows75 := by
  decide +kernel

lemma exceptionalCard75 : (candidate 10 5 0).card = 75 := by
  rw [candidate_card _ _ _ (by decide), staircase_card]

lemma exceptional_pos75 (μ : YoungDiagram) (hμ : μ.card = 75) :
    0 < kronecker (canonicalTableau (candidate 10 5 0) exceptionalCard75)
      (canonicalTableau (candidate 10 5 0) exceptionalCard75) (canonicalTableau μ hμ) := by
  apply candidate_refined_pos (r := 10) (by decide) (by decide) (by decide) rfl
    (by decide) exceptionalCard75 exceptionalRows75 (by decide) (by decide) rfl
    exceptionalPlan75 (by decide) (by decide) (by decide) (by decide) exceptionalCheck75 μ hμ

def exceptionalPlan77 : PackingPlan := (.join (.twoPaths 14 [8,8,8,8]) (.join (.neighbor 7 [4,4,4,3]) (.join (.neighbor 5 [3,3,3,2]) (.join (.repeated 1 4) (.twosOdd 6 3 [8,7])))))

def exceptionalRows77 : List ℕ := [8,8,8,8,8,7,4,4,4,4,3,3,3,3,2]

lemma exceptionalCheck77 : ∀ d ∈ List.range 4, ∀ e ∈ List.range 4,
    ∀ a ∈ List.range exceptionalRows77.length, ∀ c ∈ List.range exceptionalRows77.length,
      refinedCheck 77 10 11 (d+1) (e+1) (a+1) (c+1) exceptionalRows77 := by
  decide +kernel

lemma exceptionalCard77 : (candidate 10 5 1).card = 77 := by
  rw [candidate_card _ _ _ (by decide), staircase_card]

lemma exceptional_pos77 (μ : YoungDiagram) (hμ : μ.card = 77) :
    0 < kronecker (canonicalTableau (candidate 10 5 1) exceptionalCard77)
      (canonicalTableau (candidate 10 5 1) exceptionalCard77) (canonicalTableau μ hμ) := by
  apply candidate_refined_pos (r := 11) (by decide) (by decide) (by decide) rfl
    (by decide) exceptionalCard77 exceptionalRows77 (by decide) (by decide) rfl
    exceptionalPlan77 (by decide) (by decide) (by decide) (by decide) exceptionalCheck77 μ hμ

def exceptionalPlan79 : PackingPlan := (.join (.neighbor 15 [8,8,8,7]) (.join (.neighbor 7 [4,4,4,3]) (.join (.neighbor 5 [3,3,3,2]) (.join (.neighbor 3 [2,2,2,1]) (.twosOdd 7 1 [8,7])))))

def exceptionalRows79 : List ℕ := [8,8,8,8,7,7,4,4,4,3,3,3,3,2,2,2,2,1]

lemma exceptionalCheck79 : ∀ d ∈ List.range 4, ∀ e ∈ List.range 4,
    ∀ a ∈ List.range exceptionalRows79.length, ∀ c ∈ List.range exceptionalRows79.length,
      refinedCheck 79 10 12 (d+1) (e+1) (a+1) (c+1) exceptionalRows79 := by
  decide +kernel

lemma exceptionalCard79 : (candidate 10 6 0).card = 79 := by
  rw [candidate_card _ _ _ (by decide), staircase_card]

lemma exceptional_pos79 (μ : YoungDiagram) (hμ : μ.card = 79) :
    0 < kronecker (canonicalTableau (candidate 10 6 0) exceptionalCard79)
      (canonicalTableau (candidate 10 6 0) exceptionalCard79) (canonicalTableau μ hμ) := by
  apply candidate_refined_pos (r := 12) (by decide) (by decide) (by decide) rfl
    (by decide) exceptionalCard79 exceptionalRows79 (by decide) (by decide) rfl
    exceptionalPlan79 (by decide) (by decide) (by decide) (by decide) exceptionalCheck79 μ hμ

def exceptionalPlan81 : PackingPlan := (.join (.twoPaths 15 [9,9,8,8]) (.join (.neighbor 7 [4,4,4,3]) (.join (.neighbor 5 [3,3,3,2]) (.join (.repeated 1 4) (.twosOdd 7 3 [9,8])))))

def exceptionalRows81 : List ℕ := [9,9,9,8,8,8,4,4,4,4,3,3,3,3,2]

lemma exceptionalCheck81 : ∀ d ∈ List.range 4, ∀ e ∈ List.range 4,
    ∀ a ∈ List.range exceptionalRows81.length, ∀ c ∈ List.range exceptionalRows81.length,
      refinedCheck 81 10 13 (d+1) (e+1) (a+1) (c+1) exceptionalRows81 := by
  decide +kernel

lemma exceptionalCard81 : (candidate 10 6 1).card = 81 := by
  rw [candidate_card _ _ _ (by decide), staircase_card]

lemma exceptional_pos81 (μ : YoungDiagram) (hμ : μ.card = 81) :
    0 < kronecker (canonicalTableau (candidate 10 6 1) exceptionalCard81)
      (canonicalTableau (candidate 10 6 1) exceptionalCard81) (canonicalTableau μ hμ) := by
  apply candidate_refined_pos (r := 13) (by decide) (by decide) (by decide) rfl
    (by decide) exceptionalCard81 exceptionalRows81 (by decide) (by decide) rfl
    exceptionalPlan81 (by decide) (by decide) (by decide) (by decide) exceptionalCheck81 μ hμ

def exceptionalPlan83 : PackingPlan := (.join (.neighbor 16 [9,8,8,8]) (.join (.neighbor 7 [4,4,4,3]) (.join (.neighbor 5 [3,3,3,2]) (.join (.neighbor 3 [2,2,2,1]) (.twosOdd 8 1 [9,8])))))

def exceptionalRows83 : List ℕ := [9,9,8,8,8,8,4,4,4,3,3,3,3,2,2,2,2,1]

lemma exceptionalCheck83 : ∀ d ∈ List.range 4, ∀ e ∈ List.range 4,
    ∀ a ∈ List.range exceptionalRows83.length, ∀ c ∈ List.range exceptionalRows83.length,
      refinedCheck 83 10 14 (d+1) (e+1) (a+1) (c+1) exceptionalRows83 := by
  decide +kernel

lemma exceptionalCard83 : (candidate 10 7 0).card = 83 := by
  rw [candidate_card _ _ _ (by decide), staircase_card]

lemma exceptional_pos83 (μ : YoungDiagram) (hμ : μ.card = 83) :
    0 < kronecker (canonicalTableau (candidate 10 7 0) exceptionalCard83)
      (canonicalTableau (candidate 10 7 0) exceptionalCard83) (canonicalTableau μ hμ) := by
  apply candidate_refined_pos (r := 14) (by decide) (by decide) (by decide) rfl
    (by decide) exceptionalCard83 exceptionalRows83 (by decide) (by decide) rfl
    exceptionalPlan83 (by decide) (by decide) (by decide) (by decide) exceptionalCheck83 μ hμ

def exceptionalPlan85 : PackingPlan := (.join (.twoPaths 16 [9,9,9,9]) (.join (.neighbor 7 [4,4,4,3]) (.join (.neighbor 5 [3,3,3,2]) (.join (.repeated 1 4) (.twosOdd 8 3 [10,9])))))

def exceptionalRows85 : List ℕ := [10,9,9,9,9,9,4,4,4,4,3,3,3,3,2]

lemma exceptionalCheck85 : ∀ d ∈ List.range 4, ∀ e ∈ List.range 4,
    ∀ a ∈ List.range exceptionalRows85.length, ∀ c ∈ List.range exceptionalRows85.length,
      refinedCheck 85 10 15 (d+1) (e+1) (a+1) (c+1) exceptionalRows85 := by
  decide +kernel

lemma exceptionalCard85 : (candidate 10 7 1).card = 85 := by
  rw [candidate_card _ _ _ (by decide), staircase_card]

lemma exceptional_pos85 (μ : YoungDiagram) (hμ : μ.card = 85) :
    0 < kronecker (canonicalTableau (candidate 10 7 1) exceptionalCard85)
      (canonicalTableau (candidate 10 7 1) exceptionalCard85) (canonicalTableau μ hμ) := by
  apply candidate_refined_pos (r := 15) (by decide) (by decide) (by decide) rfl
    (by decide) exceptionalCard85 exceptionalRows85 (by decide) (by decide) rfl
    exceptionalPlan85 (by decide) (by decide) (by decide) (by decide) exceptionalCheck85 μ hμ

def exceptionalPlan87 : PackingPlan := (.join (.neighbor 17 [9,9,9,8]) (.join (.neighbor 7 [4,4,4,3]) (.join (.neighbor 5 [3,3,3,2]) (.join (.neighbor 3 [2,2,2,1]) (.twosOdd 9 1 [10,9])))))

def exceptionalRows87 : List ℕ := [10,9,9,9,9,8,4,4,4,3,3,3,3,2,2,2,2,1]

lemma exceptionalCheck87 : ∀ d ∈ List.range 4, ∀ e ∈ List.range 4,
    ∀ a ∈ List.range exceptionalRows87.length, ∀ c ∈ List.range exceptionalRows87.length,
      refinedCheck 87 10 16 (d+1) (e+1) (a+1) (c+1) exceptionalRows87 := by
  decide +kernel

lemma exceptionalCard87 : (candidate 10 8 0).card = 87 := by
  rw [candidate_card _ _ _ (by decide), staircase_card]

lemma exceptional_pos87 (μ : YoungDiagram) (hμ : μ.card = 87) :
    0 < kronecker (canonicalTableau (candidate 10 8 0) exceptionalCard87)
      (canonicalTableau (candidate 10 8 0) exceptionalCard87) (canonicalTableau μ hμ) := by
  apply candidate_refined_pos (r := 16) (by decide) (by decide) (by decide) rfl
    (by decide) exceptionalCard87 exceptionalRows87 (by decide) (by decide) rfl
    exceptionalPlan87 (by decide) (by decide) (by decide) (by decide) exceptionalCheck87 μ hμ

def exceptionalPlan106 : PackingPlan := (.join (.neighbor 18 [10,9,9,9]) (.join (.neighbor 9 [5,5,5,4]) (.join (.neighbor 7 [4,4,4,3]) (.join (.neighbor 5 [3,3,3,2]) (.join (.neighbor 3 [2,2,2,1]) (.twosOdd 8 1 [9,8]))))))

def exceptionalRows106 : List ℕ := [10,9,9,9,9,8,5,5,5,4,4,4,4,3,3,3,3,2,2,2,2,1]

lemma exceptionalCheck106 : ∀ d ∈ List.range 4, ∀ e ∈ List.range 4,
    ∀ a ∈ List.range exceptionalRows106.length, ∀ c ∈ List.range exceptionalRows106.length,
      refinedCheck 106 12 14 (d+1) (e+1) (a+1) (c+1) exceptionalRows106 := by
  decide +kernel

lemma exceptionalCard106 : (candidate 12 7 0).card = 106 := by
  rw [candidate_card _ _ _ (by decide), staircase_card]

lemma exceptional_pos106 (μ : YoungDiagram) (hμ : μ.card = 106) :
    0 < kronecker (canonicalTableau (candidate 12 7 0) exceptionalCard106)
      (canonicalTableau (candidate 12 7 0) exceptionalCard106) (canonicalTableau μ hμ) := by
  apply candidate_refined_pos (r := 14) (by decide) (by decide) (by decide) rfl
    (by decide) exceptionalCard106 exceptionalRows106 (by decide) (by decide) rfl
    exceptionalPlan106 (by decide) (by decide) (by decide) (by decide) exceptionalCheck106 μ hμ

def exceptionalPlan108 : PackingPlan := (.join (.twoPaths 18 [10,10,10,10]) (.join (.neighbor 9 [5,5,5,4]) (.join (.neighbor 7 [4,4,4,3]) (.join (.neighbor 5 [3,3,3,2]) (.join (.repeated 1 4) (.twosOdd 8 3 [10,9]))))))

def exceptionalRows108 : List ℕ := [10,10,10,10,10,9,5,5,5,4,4,4,4,4,3,3,3,3,2]

lemma exceptionalCheck108 : ∀ d ∈ List.range 4, ∀ e ∈ List.range 4,
    ∀ a ∈ List.range exceptionalRows108.length, ∀ c ∈ List.range exceptionalRows108.length,
      refinedCheck 108 12 15 (d+1) (e+1) (a+1) (c+1) exceptionalRows108 := by
  decide +kernel

lemma exceptionalCard108 : (candidate 12 7 1).card = 108 := by
  rw [candidate_card _ _ _ (by decide), staircase_card]

lemma exceptional_pos108 (μ : YoungDiagram) (hμ : μ.card = 108) :
    0 < kronecker (canonicalTableau (candidate 12 7 1) exceptionalCard108)
      (canonicalTableau (candidate 12 7 1) exceptionalCard108) (canonicalTableau μ hμ) := by
  apply candidate_refined_pos (r := 15) (by decide) (by decide) (by decide) rfl
    (by decide) exceptionalCard108 exceptionalRows108 (by decide) (by decide) rfl
    exceptionalPlan108 (by decide) (by decide) (by decide) (by decide) exceptionalCheck108 μ hμ

def exceptionalPlan110 : PackingPlan := (.join (.neighbor 19 [10,10,10,9]) (.join (.neighbor 9 [5,5,5,4]) (.join (.neighbor 7 [4,4,4,3]) (.join (.neighbor 5 [3,3,3,2]) (.join (.neighbor 3 [2,2,2,1]) (.twosOdd 9 1 [10,9]))))))

def exceptionalRows110 : List ℕ := [10,10,10,10,9,9,5,5,5,4,4,4,4,3,3,3,3,2,2,2,2,1]

lemma exceptionalCheck110 : ∀ d ∈ List.range 4, ∀ e ∈ List.range 4,
    ∀ a ∈ List.range exceptionalRows110.length, ∀ c ∈ List.range exceptionalRows110.length,
      refinedCheck 110 12 16 (d+1) (e+1) (a+1) (c+1) exceptionalRows110 := by
  decide +kernel

lemma exceptionalCard110 : (candidate 12 8 0).card = 110 := by
  rw [candidate_card _ _ _ (by decide), staircase_card]

lemma exceptional_pos110 (μ : YoungDiagram) (hμ : μ.card = 110) :
    0 < kronecker (canonicalTableau (candidate 12 8 0) exceptionalCard110)
      (canonicalTableau (candidate 12 8 0) exceptionalCard110) (canonicalTableau μ hμ) := by
  apply candidate_refined_pos (r := 16) (by decide) (by decide) (by decide) rfl
    (by decide) exceptionalCard110 exceptionalRows110 (by decide) (by decide) rfl
    exceptionalPlan110 (by decide) (by decide) (by decide) (by decide) exceptionalCheck110 μ hμ

def exceptionalPlan114 : PackingPlan := (.join (.neighbor 20 [11,10,10,10]) (.join (.neighbor 9 [5,5,5,4]) (.join (.neighbor 7 [4,4,4,3]) (.join (.neighbor 5 [3,3,3,2]) (.join (.neighbor 3 [2,2,2,1]) (.twosOdd 10 1 [11,10]))))))

def exceptionalRows114 : List ℕ := [11,11,10,10,10,10,5,5,5,4,4,4,4,3,3,3,3,2,2,2,2,1]

lemma exceptionalCheck114 : ∀ d ∈ List.range 4, ∀ e ∈ List.range 4,
    ∀ a ∈ List.range exceptionalRows114.length, ∀ c ∈ List.range exceptionalRows114.length,
      refinedCheck 114 12 18 (d+1) (e+1) (a+1) (c+1) exceptionalRows114 := by
  decide +kernel

lemma exceptionalCard114 : (candidate 12 9 0).card = 114 := by
  rw [candidate_card _ _ _ (by decide), staircase_card]

lemma exceptional_pos114 (μ : YoungDiagram) (hμ : μ.card = 114) :
    0 < kronecker (canonicalTableau (candidate 12 9 0) exceptionalCard114)
      (canonicalTableau (candidate 12 9 0) exceptionalCard114) (canonicalTableau μ hμ) := by
  apply candidate_refined_pos (r := 18) (by decide) (by decide) (by decide) rfl
    (by decide) exceptionalCard114 exceptionalRows114 (by decide) (by decide) rfl
    exceptionalPlan114 (by decide) (by decide) (by decide) (by decide) exceptionalCheck114 μ hμ

def exceptionalPlan149 : PackingPlan := (.join (.neighbor 24 [13,12,12,12]) (.join (.neighbor 11 [6,6,6,5]) (.join (.neighbor 9 [5,5,5,4]) (.join (.neighbor 7 [4,4,4,3]) (.join (.neighbor 5 [3,3,3,2]) (.join (.neighbor 3 [2,2,2,1]) (.twosOdd 12 1 [13,12])))))))

def exceptionalRows149 : List ℕ := [13,13,12,12,12,12,6,6,6,5,5,5,5,4,4,4,4,3,3,3,3,2,2,2,2,1]

lemma exceptionalCheck149 : ∀ d ∈ List.range 4, ∀ e ∈ List.range 4,
    ∀ a ∈ List.range exceptionalRows149.length, ∀ c ∈ List.range exceptionalRows149.length,
      refinedCheck 149 14 22 (d+1) (e+1) (a+1) (c+1) exceptionalRows149 := by
  decide +kernel

lemma exceptionalCard149 : (candidate 14 11 0).card = 149 := by
  rw [candidate_card _ _ _ (by decide), staircase_card]

lemma exceptional_pos149 (μ : YoungDiagram) (hμ : μ.card = 149) :
    0 < kronecker (canonicalTableau (candidate 14 11 0) exceptionalCard149)
      (canonicalTableau (candidate 14 11 0) exceptionalCard149) (canonicalTableau μ hμ) := by
  apply candidate_refined_pos (r := 22) (by decide) (by decide) (by decide) rfl
    (by decide) exceptionalCard149 exceptionalRows149 (by decide) (by decide) rfl
    exceptionalPlan149 (by decide) (by decide) (by decide) (by decide) exceptionalCheck149 μ hμ

end UniversalTensorSquare
end
end

end OAI
