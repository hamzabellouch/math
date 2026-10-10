import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Contraction.DomainSolver

namespace OAI

/-! Vector Domains Core. -/

section

open scoped BigOperators
namespace Saxl.Columns

def permVector {n : ℕ} (π : Equiv.Perm (Fin n)) : List ℕ := List.ofFn (fun i => (π i).val)

lemma permVector_get {n : ℕ} (π : Equiv.Perm (Fin n)) (i : Fin n) :
    (permVector π)[i.val]?.getD 0 = (π i).val := by
  simp [permVector,i.isLt]

lemma permVector_injective {n : ℕ} : Function.Injective (@permVector n) := by
  intro π σ h
  ext i
  have hh := congrArg (fun rs : List ℕ => rs[i.val]?.getD 0) h
  simpa only [permVector_get] using hh

lemma ofFn_fin_val (n : ℕ) : List.ofFn (fun i : Fin n => i.val) = List.range n := by
  apply List.ext_getElem
  · simp
  · intro i hi hj; simp

lemma permVector_perm {n : ℕ} (π : Equiv.Perm (Fin n)) :
    (permVector π).Perm (List.range n) := by
  simpa only [permVector,Function.comp_def,ofFn_fin_val] using π.ofFn_comp_perm (fun i : Fin n => i.val)

lemma permVector_surj {n : ℕ} {rs : List ℕ} (h : rs.Perm (List.range n)) :
    ∃ π : Equiv.Perm (Fin n), permVector π = rs := by
  obtain ⟨e,he⟩ := Saxl.list_get_equiv h
  have hl : rs.length = n := h.length_eq.trans (List.length_range)
  let π : Equiv.Perm (Fin n) := (finCongr hl.symm).trans (e.trans (finCongr (List.length_range)))
  refine ⟨π,?_⟩
  apply List.ext_getElem
  · simpa [permVector] using hl.symm
  · intro i hi hj
    have hin : i < n := by simpa only [permVector,List.length_ofFn] using hi
    have hh := he ⟨i,hj⟩
    simpa [permVector,π,List.get_eq_getElem] using hh

def vectorFull (n : ℕ) : Finset (List ℕ) :=
  ⟨(List.range n).permutations', (List.permutations_perm_permutations' _).nodup_iff.mp
    (List.nodup_permutations _ (List.nodup_range))⟩

lemma vectorFull_eq_image (n : ℕ) :
    vectorFull n = Finset.univ.image (@permVector n) := by
  ext rs
  change rs ∈ (List.range n).permutations' ↔ _
  simp only [List.mem_permutations',Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · exact permVector_surj
  · rintro ⟨π,rfl⟩; exact permVector_perm π

def vectorSign (n : ℕ) (rs : List ℕ) : ℤ :=
  ∏ x ∈ Equiv.Perm.finPairsLT n,
    if rs[x.1.val]?.getD 0 ≤ rs[x.2.val]?.getD 0 then -1 else 1

lemma sign_eq_aux {n : ℕ} (π : Equiv.Perm (Fin n)) :
    Equiv.Perm.sign π = Equiv.Perm.signAux π := by
  induction π using Equiv.Perm.swap_induction_on with
  | one => simp [Equiv.Perm.signAux_one]
  | swap_mul π i j hij ih =>
    rw [Equiv.Perm.sign_mul,Equiv.Perm.signAux_mul,ih,
      Equiv.Perm.sign_swap hij,Equiv.Perm.signAux_swap hij]

lemma vectorSign_perm {n : ℕ} (π : Equiv.Perm (Fin n)) :
    vectorSign n (permVector π) = (Equiv.Perm.sign π : ℤ) := by
  rw [sign_eq_aux]
  simp only [vectorSign,Equiv.Perm.signAux,Units.coe_prod,permVector_get]
  apply Finset.prod_congr rfl
  intro x hx
  simp only [Fin.le_def]
  split_ifs <;> rfl

def VectorDomains : List ℕ → Type
  | [] => Unit
  | _ :: rs => Finset (List ℕ) × VectorDomains rs

def VectorDomains.full : (rs : List ℕ) → VectorDomains rs
  | [] => ()
  | r :: rs => (vectorFull r,full rs)

def VectorDomains.atValue : {rs : List ℕ} → VectorDomains rs → Cells rs → ℕ → VectorDomains rs
  | _ :: _, (s,D), .inl i, j => (s.filter (fun π => π[i.val]?.getD 0 = j),D)
  | _ :: _, (s,D), .inr c, j => (s,atValue D c j)

def VectorDomains.vanished : {rs : List ℕ} → VectorDomains rs → Bool
  | [], _ => false
  | _ :: _, (s,D) => decide (s = ∅) || vanished D

def VectorDomains.mass : {rs : List ℕ} → VectorDomains rs → ℤ
  | [], _ => 1
  | r :: _, (s,D) => (∑ π ∈ s, vectorSign r π) * mass D

def Domains.encode : {rs : List ℕ} → Domains rs → VectorDomains rs
  | [], _ => ()
  | _ :: _, (s,D) => (s.image permVector,encode D)

lemma Domains.encode_full (rs : List ℕ) : (Domains.full rs).encode = VectorDomains.full rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [full,encode,VectorDomains.full,← vectorFull_eq_image,ih]; rfl

lemma Domains.encode_atValue {rs : List ℕ} (D : Domains rs) (c : Cells rs) (j : ℕ) :
    (D.atValue c j).encode = D.encode.atValue c j := by
  induction rs with
  | nil => exact c.elim
  | cons r rs ih =>
    rcases D with ⟨s,D⟩
    cases c with
    | inl i => simp only [atValue,encode,VectorDomains.atValue,Finset.filter_image,permVector_get]; rfl
    | inr c => simp only [atValue,encode,VectorDomains.atValue,ih]; rfl

lemma Domains.encode_vanished {rs : List ℕ} (D : Domains rs) : D.encode.vanished = D.vanished := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    rcases D with ⟨s,D⟩
    simp only [encode,VectorDomains.vanished,vanished,Finset.image_eq_empty,ih]

lemma Domains.encode_mass {rs : List ℕ} (D : Domains rs) : D.encode.mass = D.mass := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    rcases D with ⟨s,D⟩
    simp only [encode,VectorDomains.mass,mass,ih]
    congr 1
    rw [Finset.sum_image (fun _ _ _ _ h => permVector_injective h)]
    apply Finset.sum_congr rfl
    intro π hπ
    exact vectorSign_perm π

def vectorEdgeOptions {rsT rsA rsB : List ℕ}
    (D : VectorDomains rsT) (E : VectorDomains rsA) (F : VectorDomains rsB)
    (c : Edge rsT rsA rsB) (flag : Finset (ℕ × ℕ × ℕ)) : Finset (ℕ × ℕ × ℕ) :=
  flag.filter (fun v => (D.atValue c.1 v.1).vanished = false ∧
    (E.atValue c.2.1 v.2.1).vanished = false ∧ (F.atValue c.2.2 v.2.2).vanished = false)

lemma vectorEdgeOptions_encode {rsT rsA rsB : List ℕ}
    (D : Domains rsT) (E : Domains rsA) (F : Domains rsB)
    (c : Edge rsT rsA rsB) (flag : Finset (ℕ × ℕ × ℕ)) :
    vectorEdgeOptions D.encode E.encode F.encode c flag = edgeOptions D E F c flag := by
  simp only [vectorEdgeOptions,edgeOptions,← Domains.encode_atValue, Domains.encode_vanished]

def vectorOrderEdges {rsT rsA rsB : List ℕ}
    (D : VectorDomains rsT) (E : VectorDomains rsA) (F : VectorDomains rsB)
    (edges : List (Edge rsT rsA rsB)) (flag : Finset (ℕ × ℕ × ℕ)) : List (Edge rsT rsA rsB) :=
  bringBest (fun c => (vectorEdgeOptions D E F c flag).card) edges

lemma vectorOrderEdges_encode {rsT rsA rsB : List ℕ}
    (D : Domains rsT) (E : Domains rsA) (F : Domains rsB)
    (edges : List (Edge rsT rsA rsB)) (flag : Finset (ℕ × ℕ × ℕ)) :
    vectorOrderEdges D.encode E.encode F.encode edges flag = orderEdges D E F edges flag := by
  simp only [vectorOrderEdges,orderEdges,vectorEdgeOptions_encode]

def solveVectors {rsT rsA rsB : List ℕ} : ℕ → VectorDomains rsT → VectorDomains rsA →
    VectorDomains rsB → List (Edge rsT rsA rsB) → Finset (ℕ × ℕ × ℕ) → ℤ
  | fuel, D, E, F, edges, flag =>
    if D.vanished || E.vanished || F.vanished then 0
    else match vectorOrderEdges D E F edges flag with
      | [] => D.mass * E.mass * F.mass
      | c :: cs => match fuel with
        | 0 => 0
        | k+1 => ∑ v ∈ vectorEdgeOptions D E F c flag,
          solveVectors k (D.atValue c.1 v.1) (E.atValue c.2.1 v.2.1)
            (F.atValue c.2.2 v.2.2) cs flag

lemma solveVectors_encode {rsT rsA rsB : List ℕ} (fuel : ℕ)
    (D : Domains rsT) (E : Domains rsA) (F : Domains rsB)
    (edges : List (Edge rsT rsA rsB)) (flag : Finset (ℕ × ℕ × ℕ)) :
    solveVectors fuel D.encode E.encode F.encode edges flag = solveDomains fuel D E F edges flag := by
  induction fuel generalizing D E F edges with
  | zero =>
    rw [solveVectors,solveDomains]
    simp only [Domains.encode_vanished,vectorOrderEdges_encode,Domains.encode_mass]
    split <;> rfl
  | succ fuel ih =>
    rw [solveVectors,solveDomains]
    simp only [Domains.encode_vanished,vectorOrderEdges_encode,Domains.encode_mass]
    split
    · rfl
    · cases he : orderEdges D E F edges flag with
      | nil => rfl
      | cons c cs =>
        simp only [vectorEdgeOptions_encode,← Domains.encode_atValue,ih]

lemma contractionInteger_vectors {n : ℕ} (rsA rsB rsT : List ℕ)
    (ea : Fin n ≃ Fin rsA.sum) (eb : Fin n ≃ Fin rsB.sum) (et : Fin n ≃ Fin rsT.sum)
    (flag : Finset (ℕ × ℕ × ℕ)) :
    contractionInteger rsA rsB rsT ea eb et (fun r a b => if (r,a,b) ∈ flag then 1 else 0) =
      solveVectors n (.full rsT) (.full rsA) (.full rsB)
        (certificateEdges rsA rsB rsT ea eb et) flag := by
  rw [← Domains.encode_full,← Domains.encode_full,← Domains.encode_full, solveVectors_encode]
  exact contractionInteger_solve ..

end Saxl.Columns

end

end OAI
