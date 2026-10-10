import OAI.RingTheory.BassTrace.ClosedPaths

namespace OAI

noncomputable section

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral

namespace BassTrace.Paths

open scoped BigOperators

section

lemma mapDomain_apply_of_fibre {A B C M : Type*} [AddCommMonoid M]
    (v : A →₀ M) (d : A → B) (b : B) (j : C → A)
    (hj : Function.Injective j) (hf : ∀ a, d a = b ↔ a ∈ Set.range j) :
    (v.mapDomain d) b = ∑ᶠ c : C, v (j c) := by
  classical
  have hs : Function.support (fun a => if d a = b then v a else 0) ⊆ (v.support : Set A) := by
    intro a ha
    by_contra hnot
    apply ha
    simp [Finsupp.notMem_support_iff.mp hnot]
  calc
    (v.mapDomain d) b = ∑ a ∈ v.support, if d a = b then v a else 0 := by
      simp [Finsupp.mapDomain,Finsupp.sum,Finsupp.single_apply,eq_comm]
    _ = ∑ᶠ a : A, if d a = b then v a else 0 :=
      (finsum_eq_finsetSum_of_support_subset _ hs).symm
    _ = ∑ᶠ a ∈ Set.range j, v a := by simp only [finsum_eq_if,← hf]
    _ = ∑ᶠ c : C, v (j c) := finsum_mem_range hj

variable {G : Type*} [Group G]

def deleteLast (g : G) (n : ℕ) : Orbit g (n+1) → Orbit g n :=
  Quotient.map (fun h i => h i.castSucc) (by
    rintro h k ⟨c,hc⟩
    exact ⟨c,fun i => hc i.castSucc⟩)

def insertOrbit (g : G) (n : ℕ) (h : Fin (n+1) → G) (u : G) : Orbit g (n+1) :=
  Quotient.mk _ (Fin.snoc h u)

@[simp] lemma deleteLast_insertOrbit (g : G) (n : ℕ) (h : Fin (n+1) → G) (u : G) :
    deleteLast g n (insertOrbit g n h u) = Quotient.mk _ h := by
  change Quotient.mk (pathSetoid g n) (fun i : Fin (n+1) => Fin.snoc (α := fun _ => G) h u i.castSucc) = Quotient.mk (pathSetoid g n) h
  congr 1
  funext i
  exact Fin.snoc_castSucc (α := fun _ => G) u h i

lemma insertOrbit_injective (g : G) (n : ℕ) (h : Fin (n+1) → G) :
    Function.Injective (insertOrbit g n h) := by
  intro u v huv
  obtain ⟨c,hc⟩ := Quotient.exact huv
  have h0 := hc ((0 : Fin (n+1)).castSucc)
  simp only [Fin.snoc_castSucc] at h0
  have hc1 : (c:G) = 1 := mul_right_cancel (h0.trans (one_mul _).symm)
  have hl := hc (Fin.last (n+1))
  simpa only [Fin.snoc_last,hc1,one_mul] using hl

lemma deleteLast_fibre (g : G) (n : ℕ) (h : Fin (n+1) → G) (q : Orbit g (n+1)) :
    deleteLast g n q = Quotient.mk _ h ↔ q ∈ Set.range (insertOrbit g n h) := by
  constructor
  · induction q using Quotient.inductionOn with | _ k =>
      intro hq
      obtain ⟨c,hc⟩ := Quotient.exact hq
      refine ⟨c*k (Fin.last (n+1)), ?_⟩
      apply Eq.symm
      apply Quotient.sound
      refine ⟨c,fun i => ?_⟩
      induction i using Fin.lastCases with
      | last => simp
      | cast i => simpa only [Fin.snoc_castSucc] using hc i
  · rintro ⟨u,rfl⟩
    exact deleteLast_insertOrbit g n h u

variable {ι : Type*} [Fintype ι]

lemma pathVector_deleteLast (e : GroupMatrix (G := G) (ι := ι)) (he : e*e=e)
    (g : G) (n : ℕ) :
    (pathVector e g (n+1)).mapDomain (deleteLast g n) = pathVector e g n := by
  classical
  ext q
  induction q using Quotient.inductionOn with | _ h =>
    rw [mapDomain_apply_of_fibre _ _ _ (insertOrbit g n h)
      (insertOrbit_injective g n h) (deleteLast_fibre g n h)]
    change (∑ᶠ u, weight e g (n+1) (Fin.snoc h u)) = weight e g n h
    exact weight_snoc_finsum e he g n h

end

section

variable {G ι : Type*} [Group G] [Fintype ι]

def totalWeight (e : GroupMatrix (G := G) (ι := ι)) (g : G) (n : ℕ) : ℂ :=
  (pathVector e g n).sum fun _ z => z

lemma totalWeight_succ (e : GroupMatrix (G := G) (ι := ι)) (he : e*e=e)
    (g : G) (n : ℕ) : totalWeight e g (n+1) = totalWeight e g n := by
  unfold totalWeight
  rw [← pathVector_deleteLast e he g n]
  exact (Finsupp.sum_mapDomain_index (h := fun (_ : Orbit g n) (z : ℂ) => z)
    (fun _ => rfl) (fun _ _ _ => rfl)).symm

lemma totalWeight_eq_zeroDegree (e : GroupMatrix (G := G) (ι := ι)) (he : e*e=e)
    (g : G) (n : ℕ) : totalWeight e g n = totalWeight e g 0 := by
  induction n with
  | zero => rfl
  | succ n hn => rw [totalWeight_succ e he,hn]

def zeroConjugate (g : G) (q : Orbit g 0) : G := orbitIncrement g 0 q 0

lemma zeroConjugate_mk (g h : G) :
    zeroConjugate g (Quotient.mk _ (fun _ => h)) = h⁻¹*g*h := by
  change increment g 0 (fun _ => h) (Fin.last 0) = _
  exact increment_last g 0 _

lemma zeroConjugate_injective (g : G) : Function.Injective (zeroConjugate g) := by
  intro a b hab
  apply orbitIncrement_injective g 0
  funext i
  have hi : i = (0 : Fin 1) := Fin.ext (by omega)
  subst i
  exact hab

lemma range_zeroConjugate (g : G) : Set.range (zeroConjugate g) = {s | IsConj s g} := by
  ext s
  constructor
  · rintro ⟨q,rfl⟩
    induction q using Quotient.inductionOn with | _ h =>
      change IsConj (increment g 0 h (Fin.last 0)) g
      rw [increment_last]
      apply isConj_iff.mpr
      refine ⟨h 0, ?_⟩
      have hl : Fin.last 0 = (0 : Fin 1) := rfl
      rw [hl]
      group
  · intro hs
    obtain ⟨h,hh⟩ := isConj_iff.mp hs
    refine ⟨Quotient.mk _ (fun _ => h), ?_⟩
    rw [zeroConjugate_mk,← hh]
    group

lemma orbitWeight_zeroDegree (e : GroupMatrix (G := G) (ι := ι)) (g : G)
    (q : Orbit g 0) : orbitWeight e g 0 q = Matrix.trace (coefficient e (zeroConjugate g q)) := by
  classical
  induction q using Quotient.inductionOn with | _ h =>
    change weight e g 0 h = _
    simp only [weight,List.ofFn_succ,List.ofFn_zero,List.prod_cons,List.prod_nil,mul_one]
    rfl

lemma totalWeight_finsum (e : GroupMatrix (G := G) (ι := ι)) (g : G) (n : ℕ) :
    totalWeight e g n = ∑ᶠ q, orbitWeight e g n q := by
  classical
  exact (finsum_eq_finsetSum_of_support_subset _ (by
    intro q hq
    exact (Finsupp.mem_support_iff.mpr hq : q ∈ (pathVector e g n).support))).symm

lemma totalWeight_conjugacy (e : GroupMatrix (G := G) (ι := ι)) (he : e*e=e)
    (g : G) (n : ℕ) : totalWeight e g n =
    ∑ᶠ s ∈ {s : G | IsConj s g}, Matrix.trace (coefficient e s) := by
  rw [totalWeight_eq_zeroDegree e he,totalWeight_finsum]
  simp only [orbitWeight_zeroDegree]
  rw [← finsum_mem_range (f := fun s => Matrix.trace (coefficient e s)) (zeroConjugate_injective g),range_zeroConjugate]

end

variable {G : Type*} [Group G]

lemma twist_equivariant (g : G) (n : ℕ) (c : Subgroup.centralizer ({g} : Set G))
    (h : Fin (n+1) → G) : twist g n (fun i => c*h i) = fun i => c*twist g n h i := by
  funext i
  induction i using Fin.lastCases with
  | last =>
    simp only [twist_last]
    rw [← mul_assoc,← Subgroup.mem_centralizer_singleton_iff.mp c.property,mul_assoc]
  | cast i => simp only [twist_castSucc]

def orbitTwist (g : G) (n : ℕ) : Orbit g n → Orbit g n :=
  Quotient.map (twist g n) (by
    rintro h k ⟨c,hc⟩
    have hk : k = fun i => c*h i := funext fun i => (hc i).symm
    rw [hk,twist_equivariant]
    exact ⟨c,fun _ => rfl⟩)

lemma orbitIncrement_twist (g : G) (n : ℕ) (q : Orbit g n) :
    orbitIncrement g n (orbitTwist g n q) = orbitIncrement g n q ∘ finRotate (n+1) := by
  induction q using Quotient.inductionOn with | _ h => exact increment_twist g n h

lemma orbitTwist_injective (g : G) (n : ℕ) : Function.Injective (orbitTwist g n) := by
  intro a b hab
  apply orbitIncrement_injective g n
  have he := congrArg (orbitIncrement g n) hab
  rw [orbitIncrement_twist,orbitIncrement_twist] at he
  funext i
  obtain ⟨j,rfl⟩ := (finRotate (n+1)).surjective i
  exact congrFun he j

lemma twist_surjective (g : G) (n : ℕ) : Function.Surjective (twist g n) := by
  intro h
  refine ⟨Fin.cons (α := fun _ => G) (g⁻¹*h (Fin.last n)) (fun i => h i.castSucc), ?_⟩
  funext i
  induction i using Fin.lastCases with
  | last => simp
  | cast i => simp

lemma orbitTwist_surjective (g : G) (n : ℕ) : Function.Surjective (orbitTwist g n) := by
  intro q
  induction q using Quotient.inductionOn with | _ h =>
    obtain ⟨k,rfl⟩ := twist_surjective g n h
    exact ⟨Quotient.mk _ k,rfl⟩

variable {ι : Type*} [Fintype ι]

lemma orbitWeight_twist (e : GroupMatrix (G := G) (ι := ι)) (g : G) (n : ℕ)
    (q : Orbit g n) : orbitWeight e g n (orbitTwist g n q) = orbitWeight e g n q := by
  induction q using Quotient.inductionOn with | _ h => exact weight_twist e g n h

lemma pathVector_twist (e : GroupMatrix (G := G) (ι := ι)) (g : G) (n : ℕ) :
    (pathVector e g n).mapDomain (orbitTwist g n) = pathVector e g n := by
  ext q
  obtain ⟨p,rfl⟩ := orbitTwist_surjective g n q
  rw [Finsupp.mapDomain_apply_of_injective (orbitTwist_injective g n)]
  exact (orbitWeight_twist e g n p).symm

omit [Fintype ι] in
lemma delete_twist_tuple (g : G) (n : ℕ) (h : Fin (n+2) → G) (i : Fin (n+1)) :
    (fun j => twist g (n+1) h (i.castSucc.succAbove j)) =
      twist g n (fun j => h (i.succ.succAbove j)) := by
  funext j
  induction j using Fin.lastCases with
  | last => simp only [Fin.succAbove_ne_last_last (Fin.castSucc_ne_last i),twist_last,
      Fin.succAbove_ne_zero_zero (Fin.succ_ne_zero i)]
  | cast j =>
    rw [Fin.castSucc_succAbove_castSucc]
    simp only [twist_castSucc,Fin.succ_succAbove_succ]

def deleteEntry (g : G) (n : ℕ) (i : Fin (n+2)) : Orbit g (n+1) → Orbit g n :=
  Quotient.map (fun h j => h (i.succAbove j)) (by
    rintro h k ⟨c,hc⟩
    exact ⟨c,fun j => hc (i.succAbove j)⟩)

omit [Fintype ι] in
lemma deleteEntry_zero (g : G) (n : ℕ) :
    deleteEntry g n 0 = deleteLast g n ∘ orbitTwist g (n+1) := by
  funext q
  induction q using Quotient.inductionOn with | _ h =>
    change Quotient.mk (pathSetoid g n) (fun j => h j.succ) =
      Quotient.mk (pathSetoid g n) (fun j => twist g (n+1) h j.castSucc)
    simp only [twist_castSucc]

omit [Fintype ι] in
lemma deleteEntry_castSucc_twist (g : G) (n : ℕ) (i : Fin (n+1)) :
    deleteEntry g n i.castSucc ∘ orbitTwist g (n+1) =
      orbitTwist g n ∘ deleteEntry g n i.succ := by
  funext q
  induction q using Quotient.inductionOn with | _ h =>
    change Quotient.mk (pathSetoid g n) (fun j => twist g (n+1) h (i.castSucc.succAbove j)) =
      Quotient.mk (pathSetoid g n) (twist g n (fun j => h (i.succ.succAbove j)))
    rw [delete_twist_tuple]

lemma pathVector_deleteEntry (e : GroupMatrix (G := G) (ι := ι)) (he : e*e=e)
    (g : G) (n : ℕ) (i : Fin (n+2)) :
    (pathVector e g (n+1)).mapDomain (deleteEntry g n i) = pathVector e g n := by
  induction i using Fin.induction with
  | zero =>
    rw [deleteEntry_zero,Finsupp.mapDomain_comp,pathVector_twist,pathVector_deleteLast e he]
  | succ i hi =>
    apply Finsupp.mapDomain_injective (orbitTwist_injective g n)
    rw [← Finsupp.mapDomain_comp,← deleteEntry_castSucc_twist,Finsupp.mapDomain_comp,
      pathVector_twist,hi,pathVector_twist]

end BassTrace.Paths

end

end OAI
