import Mathlib
import OAI.SetTheory.PartitionConsistency.Construction.CompleteRounds

namespace OAI

/-! ## SaturationData -/

namespace PartitionConsistency.MonoidConstruction
universe u
open CategoryTheory CategoryTheory.Limits DiagramOrder DiagramForcing
noncomputable section
open scoped Classical

@[ext] theorem _root_.OAI.PartitionConsistency.DiagramForcing.OverlapPrescription.ext
    {A : Type u} {n : ℕ} {P Q : OverlapPrescription A n}
    (h : ∀ i j, P.start i j = Q.start i j) : P = Q := by
  cases P; cases Q; congr 1; exact funext (fun i => funext (h i))

namespace Saturation
variable (M : Object.{u}) (K : Type u) [Nonempty K]

/-- All the parameters of a final probe occur before one complete round.
Its comparisons reflect to that stage; they are not separately postulated. -/
theorem probe_stage (d : ProbeData (target M K)) :
    ∃ j : OuterIndex.{u}, j < ⊤ ∧ ∃ d₀ : ProbeData ((tower M K).obj j),
      fromStage M K j d₀.a = d.a ∧ fromStage M K j d₀.b = d.b ∧
        ∀ i, fromStage M K j (d₀.path.node i) = d.path.node i := by
  let f : Option (Option ℕ) → target M K
    | none => d.b
    | some none => d.a
    | some (some n) => d.path.node n
  obtain ⟨j,hj,g,hg⟩ := countable_stage M K f
  let f₀ := fromStage M K j
  let P : ProbeAlgebra.Path ((tower M K).obj j) (g (some none)) := {
    node := fun i => g (some (some i))
    zero := by
      apply f₀.injective
      exact (hg (some (some 0))).trans (d.path.zero.trans f₀.map_one.symm)
    increasing := by
      intro i k hik
      apply (f₀.conservative.dvd_iff _ _).1
      simpa only [f₀,hg,f] using d.path.increasing hik
    bounded := by
      intro i
      apply (f₀.conservative.dvd_iff _ _).1
      simpa only [f₀,hg,f] using d.path.bounded i }
  refine ⟨j,hj,⟨g (some none),g none,?_,P⟩,hg (some none),hg none,fun i => hg (some (some i))⟩
  intro he
  apply d.b_ne_one
  exact (hg none).symm.trans ((congrArg f₀ he).trans f₀.map_one)

/-- Inclusion of the completed successor round into the final union. -/
def afterRound (j : OuterIndex.{u}) (hj : j < ⊤) :
    CompleteRound.target ((tower M K).obj j) K ⟶ target M K :=
  (succIso M K j hj).inv ≫ fromStage M K (Order.succ j)

theorem inclusion_afterRound (j : OuterIndex.{u}) (hj : j < ⊤) :
    CompleteRound.inclusion ((tower M K).obj j) K ≫ afterRound M K j hj =
      fromStage M K j := by
  unfold afterRound
  rw [← Category.assoc,← map_succ]
  unfold fromStage
  erw [← Functor.map_comp,homOfLE_comp]

theorem afterRound_preservesProfiles (j : OuterIndex.{u}) (hj : j < ⊤) :
    PreservesProfiles (afterRound M K j hj) :=
  (PreservesProfiles.of_iso (succIso M K j hj).symm).comp
    (preservesProfiles M K _ _ _)

/-- Saturation for countable paths, including the complete final divisor
profile and pairwise exact intersections in the final monoid. -/
theorem probes (d : ProbeData (target M K)) :
    ∃ m : K → target M K, Function.Injective m ∧
      (∀ i, ProbeProfile d.a d.b (target M K).e (m i) d.path.node) ∧
      ∀ i j, i ≠ j → ∀ z : target M K,
        m i ∣ z ∧ m j ∣ z ↔ d.a * (target M K).e ∣ z := by
  obtain ⟨j,hj,d₀,ha,hb,hn⟩ := probe_stage M K d
  let f := afterRound M K j hj
  let C := CompleteRound.target ((tower M K).obj j) K
  let inc := CompleteRound.inclusion ((tower M K).obj j) K
  have hi (x : (tower M K).obj j) : f (inc x) = fromStage M K j x :=
    congrArg (fun h : (tower M K).obj j ⟶ target M K => h x) (inclusion_afterRound M K j hj)
  have he : f C.e = (target M K).e := f.map_e
  let m : K → C := CompleteRound.probe ((tower M K).obj j) K d₀
  refine ⟨fun i => f (m i),f.injective.comp (CompleteRound.probe_injective _ K d₀),?_,?_⟩
  · intro i
    have ht := afterRound_preservesProfiles M K j hj _ _ _ _ _
      (CompleteRound.probe_profile _ K d₀ i)
    change ProbeProfile (f (inc d₀.a)) (f (inc d₀.b)) (f C.e)
      (f (m i)) (fun k => f (inc (d₀.path.node k))) at ht
    simpa only [hi,ha,hb,he,hn] using ht
  · intro i k hik z
    have hh := f.conservative.intersections (m i) (m k) (inc d₀.a * C.e)
      (CompleteRound.probes_independent _ K d₀ i k hik) z
    simpa only [f.map_mul,hi,ha,he] using hh

/-- Every finite prescription, without a validity restriction, is the image
of its actual parameters in a proper stage. -/
theorem prescription_stage {n : ℕ} (P : OverlapPrescription (target M K) n) :
    ∃ j : OuterIndex.{u}, j < ⊤ ∧ ∃ P₀ : OverlapPrescription ((tower M K).obj j) n,
      P₀.map (fromStage M K j).toMonoidHom = P := by
  let f : Fin n × Fin n × Bool → target M K := fun (i,k,b) =>
    if b then ((P.start i k).getD (1,1)).2 else ((P.start i k).getD (1,1)).1
  obtain ⟨j,hj,g,hg⟩ := countable_stage M K f
  let P₀ : OverlapPrescription ((tower M K).obj j) n :=
    ⟨fun i k => (P.start i k).map (fun _ => (g (i,k,false),g (i,k,true)))⟩
  refine ⟨j,hj,P₀,?_⟩
  apply OverlapPrescription.ext
  intro i k
  cases hp : P.start i k with
  | none => simp [P₀,OverlapPrescription.map,hp]
  | some ab =>
    have ha := hg (i,k,false)
    have hb := hg (i,k,true)
    simp only [f,hp,Option.getD_some,Bool.false_eq_true,↓reduceIte] at ha
    simp only [f,hp,Option.getD_some,↓reduceIte] at hb
    simp only [OverlapPrescription.map_start,P₀,hp,Option.map_some,ha,hb,Prod.eta]

/-- Exact cone realizations persist after all the later rounds, including
for right factors which did not exist when the merger was executed. -/
theorem realizes_prescription {n : ℕ} (P : OverlapPrescription (target M K) n)
    (hP : P.Valid) : ∃ l : Fin n → target M K, P.RootSystem l := by
  by_cases hn : 0 < n
  · obtain ⟨j,hj,P₀,hmap⟩ := prescription_stage M K P
    have hv : P₀.Valid := P₀.valid_of_map (fromStage M K j).conservative (hmap ▸ hP)
    let d : MergerData ((tower M K).obj j) := ⟨n,hn,P₀,hv⟩
    obtain ⟨l,hl⟩ := CompleteRound.realizes_merger ((tower M K).obj j) K d
    let f := afterRound M K j hj
    have ht := hl.map f.conservative
    have hp : (d.prescription.map (CompleteRound.inclusion ((tower M K).obj j) K).toMonoidHom).map
        f.toMonoidHom = P := by
      rw [← hmap]
      apply OverlapPrescription.ext
      intro i k
      change ((P₀.start i k).map _).map _ = (P₀.start i k).map _
      rw [Option.map_map]
      apply congrArg (fun g => (P₀.start i k).map g)
      funext ab
      have h := inclusion_afterRound M K j hj
      exact congrArg (fun t : (tower M K).obj j ⟶ target M K => (t ab.1,t ab.2)) h
    exact ⟨fun i => f (l i),hp ▸ ht⟩
  · have hn : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    exact ⟨Fin.elim0,fun i => Fin.elim0 i⟩

theorem finiteMergers : HasFiniteMergers (target M K) := by
  intro n P hP
  obtain ⟨l,hl⟩ := realizes_prescription M K P hP
  exact ⟨l,hl.realization⟩

/-- The final ideal requirement uses all divisors in the final monoid, not
only those belonging to the scheduling stage. -/
theorem ideal_probes (a b : target M K) (hb : b ≠ 1)
    (U : ConeIdeal (α := LeftDivOrder (target M K)) a) :
    ∃ m : K → target M K, Function.Injective m ∧
      (∀ i, m i * b = a * (target M K).e ∧ ¬ m i ∣ a ∧
        (∀ x : target M K, x ∣ a ∧ x ∣ m i ↔ x ∈ U.carrier) ∧
        ∀ x : target M K, x ∣ a → x ∉ U.carrier →
          ∀ z : target M K, x ∣ z ∧ m i ∣ z ↔ a * (target M K).e ∣ z) ∧
      ∀ i j, i ≠ j → ∀ z : target M K,
        m i ∣ z ∧ m j ∣ z ↔ a * (target M K).e ∣ z := by
  obtain ⟨p,hp₀,hpU,hpinc,hpcof⟩ := U.countable_cofinal_sequence (target M K).margin (target M K).joins
  let path : ProbeAlgebra.Path (target M K) a := ⟨p,hp₀,fun {i j} h => (LeftDivOrder.le_iff_dvd _ _).1 (hpinc h),
    fun i => (LeftDivOrder.le_iff_dvd _ _).1 (U.bounded (hpU i))⟩
  let d : ProbeData (target M K) := ⟨a,b,hb,path⟩
  obtain ⟨m,hminj,hm,hind⟩ := probes M K d
  refine ⟨m,hminj,fun i => ?_,hind⟩
  refine ⟨(hm i).exit,(hm i).not_divides,?_,?_⟩
  · intro x
    rw [(hm i).divisors]
    exact ⟨fun ⟨n,hn⟩ => U.lower ((LeftDivOrder.le_iff_dvd _ _).2 hn) (hpU n),
      fun hx => (hpcof x hx).imp (fun n hn => (LeftDivOrder.le_iff_dvd _ _).1 hn)⟩
  · intro x hxa hxu
    apply (hm i).joins x hxa
    intro hxm
    obtain ⟨n,hn⟩ := ((hm i).divisors x).1 ⟨hxa,hxm⟩
    exact hxu (U.lower ((LeftDivOrder.le_iff_dvd _ _).2 hn) (hpU n))

/-- The executed probes at `a = 1, b = e` lie outside the full cone `eT`. -/
theorem complement_probes : ∃ m : K → target M K,
    Function.Injective m ∧ ∀ i, ¬ (target M K).e ∣ m i := by
  let d : ProbeData (target M K) := {
    a := 1
    b := (target M K).e
    b_ne_one := (target M K).e_ne_one
    path := ⟨fun _ => 1,rfl,fun _ => dvd_refl _,fun _ => dvd_refl _⟩ }
  obtain ⟨m,hinj,hm,hind⟩ := probes M K d
  refine ⟨m,hinj,?_⟩
  intro i he
  obtain ⟨x,hx⟩ := he
  have hex : (target M K).e * x * (target M K).e = 1 * (target M K).e := by
    rw [← hx]; exact (hm i).exit
  have hxe : x * (target M K).e = 1 := by
    apply mul_left_cancel (a := (target M K).e)
    simpa only [mul_assoc,mul_one,one_mul] using hex
  exact (target M K).e_ne_one (IsConical.eq_one_of_mul_eq_one hxe).2

theorem target_cardinal {μ : Cardinal.{u}} (hω : Cardinal.aleph 1 ≤ μ)
    (hpow : μ ^ Cardinal.aleph0 = μ) (hM : Cardinal.mk M ≤ μ) (hK : Cardinal.mk K = μ) :
    Cardinal.mk (target M K) = μ := by
  apply le_antisymm (cardinal_le M K hω hpow hM hK.le ⊤)
  obtain ⟨m,hinj,_⟩ := complement_probes M K
  rw [← hK]
  exact Cardinal.mk_le_of_injective hinj

theorem complement_cardinal {μ : Cardinal.{u}} (hω : Cardinal.aleph 1 ≤ μ)
    (hpow : μ ^ Cardinal.aleph0 = μ) (hM : Cardinal.mk M ≤ μ) (hK : Cardinal.mk K = μ) :
    Cardinal.mk {x : target M K // ¬ (target M K).e ∣ x} = μ := by
  apply le_antisymm
  · exact (Cardinal.mk_subtype_le _).trans (cardinal_le M K hω hpow hM hK.le ⊤)
  · obtain ⟨m,hinj,hm⟩ := complement_probes M K
    rw [← hK]
    exact Cardinal.mk_le_of_injective (f := fun i => (⟨m i,hm i⟩ : {x // ¬ (target M K).e ∣ x}))
      (fun i j h => hinj (congrArg Subtype.val h))

end Saturation
end
end PartitionConsistency.MonoidConstruction

end OAI
