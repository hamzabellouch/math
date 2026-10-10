import Mathlib
import OAI.SetTheory.PartitionConsistency.Construction.MonoidRounds
import OAI.SetTheory.PartitionConsistency.Algebra.ProbePresentations

namespace OAI

/-! ## RequestSize -/
namespace PartitionConsistency.MonoidConstruction
universe u
noncomputable section
open scoped Classical

namespace ProbeData
variable {M : Object.{u}}
def code (d : ProbeData M) : M × M × (ℕ → M) := (d.a,d.b,d.path.node)
theorem code_injective : Function.Injective (code (M := M)) := by
  rintro ⟨a,b,hb,⟨n,h0,hi,ha⟩⟩ ⟨a',b',hb',⟨n',h0',hi',ha'⟩⟩ h
  obtain ⟨rfl,rfl,rfl⟩ := (Prod.mk.inj h).imp_right (fun h => Prod.mk.inj h)
  rfl

theorem data_cardinal_le {μ : Cardinal.{u}} (hω : Cardinal.aleph0 ≤ μ)
    (hpow : μ ^ Cardinal.aleph0 = μ) (hM : Cardinal.mk M ≤ μ) :
    Cardinal.mk (ProbeData M) ≤ μ := by
  apply (Cardinal.mk_le_of_injective (code_injective (M := M))).trans
  simp only [Cardinal.mk_prod,Cardinal.mk_arrow,Cardinal.mk_nat,Cardinal.lift_id,Cardinal.lift_id',
    Cardinal.lift_aleph0]
  have hp : Cardinal.mk M ^ Cardinal.aleph0 ≤ μ := by
    rw [← hpow]; exact Cardinal.power_le_power_right hM
  exact (mul_le_mul' hM (mul_le_mul' hM hp)).trans_eq
    (by rw [Cardinal.mul_eq_self hω,Cardinal.mul_eq_self hω])
end ProbeData

namespace MergerData
variable {M : Object.{u}}
def code (d : MergerData M) : Σ n : ℕ, Fin n → Fin n → Option (M × M) :=
  ⟨d.n,d.prescription.start⟩

theorem code_injective : Function.Injective (code (M := M)) := by
  rintro ⟨n,hn,⟨p⟩,hp⟩ ⟨n',hn',⟨p'⟩,hp'⟩ h
  have hn : n = n' := congrArg Sigma.fst h
  subst n'
  have hh : p = p' := eq_of_heq (Sigma.mk.inj h).2
  subst p'
  rfl

theorem data_cardinal_le {μ : Cardinal.{u}} (hω : Cardinal.aleph0 ≤ μ)
    (hpow : μ ^ Cardinal.aleph0 = μ) (hM : Cardinal.mk M ≤ μ) :
    Cardinal.mk (MergerData M) ≤ μ := by
  have hμ : μ ≠ 0 := ne_of_gt (Cardinal.aleph0_pos.trans_le hω)
  have hu : Cardinal.mk (Option (M × M)) ≤ μ := by
    simp only [Cardinal.mk_option,Cardinal.mk_prod,Cardinal.lift_id]
    exact (add_le_add ((mul_le_mul' hM hM).trans_eq (Cardinal.mul_eq_self hω))
      (Cardinal.one_le_aleph0.trans hω)).trans_eq (Cardinal.add_eq_self hω)
  have hn (n : ℕ) : Cardinal.mk (Fin n → Fin n → Option (M × M)) ≤ μ := by
    have hf : Cardinal.lift.{u} (Cardinal.mk (Fin n)) ≤ μ :=
      (Cardinal.lift_le.2 Cardinal.mk_le_aleph0).trans (by simpa using hω)
    have hfω : Cardinal.lift.{u} (Cardinal.mk (Fin n)) ≤ Cardinal.aleph0 := by
      simp
    have h : (Cardinal.mk (Option (M × M))) ^ Cardinal.lift.{u} (Cardinal.mk (Fin n)) ≤ μ :=
      ((Cardinal.power_le_power_right hu).trans (Cardinal.power_le_power_left hμ hfω)).trans_eq hpow
    simp only [Cardinal.mk_arrow,Cardinal.lift_id']
    exact ((Cardinal.power_le_power_right h).trans
      (Cardinal.power_le_power_left hμ hfω)).trans_eq hpow
  apply (Cardinal.mk_le_of_injective (code_injective (M := M))).trans
  rw [Cardinal.mk_sigma]
  apply (Cardinal.sum_le_sum _ (fun _ : ℕ => μ) hn).trans
  simpa only [Cardinal.sum_const,Cardinal.mk_nat,Cardinal.lift_aleph0,
    Cardinal.lift_id',Cardinal.lift_umax,Cardinal.mul_eq_self hω] using (mul_le_mul_left hω μ)
end MergerData

namespace Request
variable {M : Object.{u}}
theorem data_cardinal_le {μ : Cardinal.{u}} (hω : Cardinal.aleph0 ≤ μ)
    (hpow : μ ^ Cardinal.aleph0 = μ) (hM : Cardinal.mk M ≤ μ) :
    Cardinal.mk (Request M) ≤ μ := by
  rw [Cardinal.mk_sum]
  simp only [Cardinal.lift_id]
  exact (add_le_add (ProbeData.data_cardinal_le hω hpow hM)
    (MergerData.data_cardinal_le hω hpow hM)).trans_eq (Cardinal.add_eq_self hω)
end Request
end
end PartitionConsistency.MonoidConstruction


/-! ## MergerPersistence -/
namespace PartitionConsistency
universe u v
noncomputable section
open scoped Classical
open DiagramOrder

namespace MergerAlgebra.Word
variable {M : Type u} {D : Type v} [LeftCancelMonoid M] [IsConical M]
  [RightFreeAction M D]
omit [IsConical M] in
/-- Disjoint terminal-letter cones give disjoint cones with any fixed prefix. -/
theorem snoc_cones_disjoint (w : Word M D) (s t : D)
    (hst : ∀ d : D, ¬ (RightFreeAction.Reaches M s d ∧ RightFreeAction.Reaches M t d))
    (z : Word M D) : ¬ (snoc w s ∣ z ∧ snoc w t ∣ z) := by
  induction z with
  | old x => simp only [snoc_not_dvd_old,false_and,not_false_eq_true]
  | snoc z d ih =>
    simp only [snoc_dvd_snoc_iff]
    by_cases hw : w = z
    · subst z
      simpa only [snoc_not_dvd_prefix,true_and,false_or] using hst d
    · simpa only [hw,false_and,or_false] using ih
end MergerAlgebra.Word

namespace DiagramForcing.OverlapPrescription
variable {M : Type u} [LeftCancelMonoid M] {n : ℕ}
/-- The cone form of exact realization. Unlike checking only old right factors,
this form persists under arbitrary conservative embeddings. -/
def RootSystem (P : OverlapPrescription M n) (l : Fin n → M) : Prop :=
  ∀ i j, i ≠ j → match P.start i j with
    | none => ∀ z : M, ¬ (l i ∣ z ∧ l j ∣ z)
    | some (a,b) => l i * a = l j * b ∧ ∀ z : M, l i ∣ z ∧ l j ∣ z ↔ l i * a ∣ z

namespace RootSystem
variable {P : OverlapPrescription M n} {l : Fin n → M}
theorem map {N : Type v} [LeftCancelMonoid N] {f : M →* N} (hf : Conservative f)
    (h : P.RootSystem l) : (P.map f).RootSystem (fun i => f (l i)) := by
  intro i j hij
  have h := h i j hij
  cases he : P.start i j with
  | none =>
    simp only [map_start,he,Option.map_none]
    intro z hz
    obtain ⟨x,hx⟩ := hf.common (l i) (l j) ⟨z,hz⟩
    exact (he ▸ h) x hx
  | some ab =>
    obtain ⟨a,b⟩ := ab
    simp only [he] at h
    simp only [map_start,he,Option.map_some]
    exact ⟨by simpa only [f.map_mul] using congrArg f h.1,
      fun z => by simpa only [f.map_mul] using hf.intersections (l i) (l j) (l i * a) h.2 z⟩

theorem realization (h : P.RootSystem l) (z w : Fin n × M) :
    l z.1 * z.2 = l w.1 * w.2 ↔ P.Rel z w := by
  obtain ⟨i,x⟩ := z; obtain ⟨j,y⟩ := w
  by_cases hij : i = j
  · subst j
    simp only [rel_same_copy,mul_left_cancel_iff]
  · have hspec := h i j hij
    simp only [Rel,hij,↓reduceIte]
    cases he : P.start i j with
    | none =>
      simp only
      constructor
      · intro heq
        exact (he ▸ hspec) (l i * x) ⟨dvd_mul_right _ _,heq.symm ▸ dvd_mul_right (l j) y⟩
      · exact False.elim
    | some ab =>
      obtain ⟨a,b⟩ := ab
      simp only [he] at hspec ⊢
      constructor
      · intro heq
        obtain ⟨t,ht⟩ := (hspec.2 (l i * x)).1
          ⟨dvd_mul_right _ _,heq.symm ▸ dvd_mul_right (l j) y⟩
        refine ⟨t,mul_left_cancel (ht.trans (mul_assoc _ _ _)),?_⟩
        apply mul_left_cancel (a := l j)
        rw [← heq,ht,hspec.1,mul_assoc]
      · rintro ⟨t,rfl,rfl⟩
        rw [← mul_assoc,hspec.1,mul_assoc]
end RootSystem

variable [IsConical M]
open MergerAlgebra MergerAlgebra.RightFreeAction
omit [IsConical M] in
/-- A literal merger realizes prescribed cones in its entire normal-form monoid,
not only at the old factors. -/
theorem root_system (P : OverlapPrescription M n) (hP : P.Valid) :
    (P.map (Word.oldHom : M →* P.Merger hP)).RootSystem (P.root hP) := by
  intro i j hij
  cases he : P.start i j with
  | none =>
    simp only [map_start,he,Option.map_none]
    apply Word.snoc_cones_disjoint
    rintro d ⟨⟨x,hx⟩,⟨y,hy⟩⟩
    have h := (P.copy_eq_iff hP i j (1*x) (1*y)).1 (hx.trans hy.symm)
    simp only [Rel,hij,↓reduceIte,he] at h
  | some ab =>
    obtain ⟨a,b⟩ := ab
    simp only [map_start,he,Option.map_some]
    refine ⟨(P.root_mul_eq_iff hP (i,a) (j,b)).2 ?_,?_⟩
    · simp only [Rel,hij,↓reduceIte,he]
      exact ⟨1,(mul_one _).symm,(mul_one _).symm⟩
    · have hletters (z : P.Copies hP) :
          Reaches M (P.copy hP i 1) z ∧ Reaches M (P.copy hP j 1) z ↔
            Reaches M (P.copy hP i a) z := by
        rw [P.overlap_cone_intersection hP hij he]
        constructor
        · rintro ⟨t,_,_,hz⟩
          exact ⟨t,hz.symm⟩
        · rintro ⟨t,ht⟩
          exact ⟨t,one_dvd _,one_dvd _,ht.symm⟩
      intro z
      change P.root hP i ∣ z ∧ P.root hP j ∣ z ↔ P.root hP i * Word.old a ∣ z
      rw [root_mul_old]
      exact Word.snoc_cone_intersection (Word.old (1 : M)) _ _ _ hletters z

end DiagramForcing.OverlapPrescription

namespace MonoidConstruction.MergerData
variable {M : MonoidConstruction.Object.{u}} (d : MonoidConstruction.MergerData M)
theorem cone_realization : (d.prescription.map d.inclusion.toMonoidHom).RootSystem d.root :=
  d.prescription.root_system d.valid
end MonoidConstruction.MergerData
end
end PartitionConsistency


/-! ## RoundExecution -/
namespace PartitionConsistency
universe u v w
open CategoryTheory CategoryTheory.Limits DiagramOrder
noncomputable section
open scoped Classical
namespace DiagramForcing.OverlapPrescription
variable {M : Type u} {N : Type v} {R : Type w} [Monoid M] [Monoid N] [Monoid R]
@[simp] theorem map_comp {n : ℕ} (P : OverlapPrescription M n) (f : M →* N) (g : N →* R) :
    (P.map f).map g = P.map (g.comp f) := by
  apply OverlapPrescription.mk.injEq _ _ |>.mpr
  funext i j
  cases h : P.start i j <;> simp [map_start,h]
end DiagramForcing.OverlapPrescription

namespace MonoidConstruction.Round
variable {J : Type u} [CompleteLinearOrder J] [SuccOrder J] [WellFoundedLT J]
  (M : Object.{u}) (schedule : J → Request M)

/-- Identification of the next stage with the actual operation's normal forms. -/
def requestIso (j : J) (hj : ¬IsMax j) (d : Request M) (hd : schedule j = d) :
    (functor M schedule).obj (Order.succ j) ≅ (d.map (fromBase M schedule j)).target :=
  succIso M schedule j hj ≪≫ eqToIso (by rw [hd])

theorem map_succ_request (j : J) (hj : ¬IsMax j) (d : Request M) (hd : schedule j = d) :
    (functor M schedule).map (homOfLE (Order.le_succ j)) =
      (d.map (fromBase M schedule j)).inclusion ≫ (requestIso M schedule j hj d hd).inv := by
  rw [map_succ M schedule j hj]
  dsimp only [requestIso,Iso.trans_inv]
  rw [← Category.assoc]
  congr 1
  exact Request.inclusion_eq_transport _ _ (congrArg (fun r => r.map (fromBase M schedule j)) hd)

def afterRequestMap (j : J) (hj : ¬IsMax j) (d : Request M) (hd : schedule j = d)
    (k : J) (hjk : Order.succ j ≤ k) :
    (d.map (fromBase M schedule j)).target ⟶ (functor M schedule).obj k :=
  (requestIso M schedule j hj d hd).inv ≫ (functor M schedule).map (homOfLE hjk)

theorem inclusion_afterRequestMap (j : J) (hj : ¬IsMax j) (d : Request M) (hd : schedule j = d)
    (k : J) (hjk : Order.succ j ≤ k) :
    (d.map (fromBase M schedule j)).inclusion ≫ afterRequestMap M schedule j hj d hd k hjk =
      (functor M schedule).map (homOfLE ((Order.le_succ j).trans hjk)) := by
  dsimp only [afterRequestMap]
  rw [← Category.assoc,← map_succ_request,← Functor.map_comp,homOfLE_comp]

theorem fromBase_afterRequestMap (j : J) (hj : ¬IsMax j) (d : Request M) (hd : schedule j = d)
    (k : J) (hjk : Order.succ j ≤ k) (x : M) :
    afterRequestMap M schedule j hj d hd k hjk
      ((d.map (fromBase M schedule j)).inclusion (fromBase M schedule j x)) =
        fromBase M schedule k x := by
  change (fromBase M schedule j ≫ (d.map (fromBase M schedule j)).inclusion ≫
    afterRequestMap M schedule j hj d hd k hjk) x = _
  rw [inclusion_afterRequestMap,fromBase_naturality]

theorem afterRequestMap_preservesProfiles (j : J) (hj : ¬IsMax j) (d : Request M) (hd : schedule j = d)
    (k : J) (hjk : Order.succ j ≤ k) :
    PreservesProfiles (afterRequestMap M schedule j hj d hd k hjk) :=
  (PreservesProfiles.of_iso (requestIso M schedule j hj d hd).symm).comp
    (preservesProfiles M schedule _ _ hjk)

/-- Each scheduled finite merger stays exact at every subsequent cut,
including for the new right factors at that cut. -/
theorem creates_merger (j : J) (hj : ¬IsMax j) (d : MergerData M)
    (hd : schedule j = .inr d) (k : J) (hjk : Order.succ j ≤ k) :
    ∃ l : Fin d.n → (functor M schedule).obj k,
      (d.prescription.map (fromBase M schedule k).toMonoidHom).RootSystem l := by
  let d' := d.map (fromBase M schedule j)
  let f : d'.extension ⟶ (functor M schedule).obj k :=
    afterRequestMap M schedule j hj (.inr d) hd k hjk
  refine ⟨fun i => f (d'.root i),?_⟩
  have h := d'.cone_realization.map f.conservative
  have he : (f.toMonoidHom.comp d'.inclusion.toMonoidHom).comp
      (fromBase M schedule j).toMonoidHom = (fromBase M schedule k).toMonoidHom := by
    ext x
    exact fromBase_afterRequestMap M schedule j hj (.inr d) hd k hjk x
  change (((d.prescription.map (fromBase M schedule j).toMonoidHom).map
    d'.inclusion.toMonoidHom).map f.toMonoidHom).RootSystem _ at h
  simp only [DiagramForcing.OverlapPrescription.map_comp,← MonoidHom.comp_assoc,he] at h
  exact h

/-- The actual new probe after its conservative transport to a later cut. -/
def probe (j : J) (hj : ¬IsMax j) (d : ProbeData M)
    (hd : schedule j = .inl d) (k : J) (hjk : Order.succ j ≤ k) :
    (functor M schedule).obj k :=
  afterRequestMap M schedule j hj (.inl d) hd k hjk (d.map (fromBase M schedule j)).probe

@[simp] theorem probe_transition (j : J) (hj : ¬IsMax j) (d : ProbeData M)
    (hd : schedule j = .inl d) (k l : J) (hjk : Order.succ j ≤ k) (hkl : k ≤ l) :
    (functor M schedule).map (homOfLE hkl) (probe M schedule j hj d hd k hjk) =
      probe M schedule j hj d hd l (hjk.trans hkl) := by
  change ((requestIso M schedule j hj (.inl d) hd).inv ≫
    (functor M schedule).map (homOfLE hjk) ≫ (functor M schedule).map (homOfLE hkl)) _ = _
  rw [← Functor.map_comp,homOfLE_comp]
  rfl

theorem probe_profile (j : J) (hj : ¬IsMax j) (d : ProbeData M)
    (hd : schedule j = .inl d) (k : J) (hjk : Order.succ j ≤ k) :
    ProbeProfile (fromBase M schedule k d.a) (fromBase M schedule k d.b)
      ((functor M schedule).obj k).e (probe M schedule j hj d hd k hjk)
      (fun i => fromBase M schedule k (d.path.node i)) := by
  let f := afterRequestMap M schedule j hj (.inl d) hd k hjk
  have hp := afterRequestMap_preservesProfiles M schedule j hj (.inl d) hd k hjk
    _ _ _ _ _ (d.map (fromBase M schedule j)).profile
  change ProbeProfile (f ((d.map (fromBase M schedule j)).inclusion (fromBase M schedule j d.a)))
    (f ((d.map (fromBase M schedule j)).inclusion (fromBase M schedule j d.b)))
    (f ((d.map (fromBase M schedule j)).extension.e)) (probe M schedule j hj d hd k hjk)
    (fun i => f ((d.map (fromBase M schedule j)).inclusion (fromBase M schedule j (d.path.node i)))) at hp
  have he (x : M) : f ((d.map (fromBase M schedule j)).inclusion (fromBase M schedule j x)) =
      fromBase M schedule k x := fromBase_afterRequestMap M schedule j hj (.inl d) hd k hjk x
  have hee : f (d.map (fromBase M schedule j)).extension.e = ((functor M schedule).obj k).e := f.map_e
  simpa only [he,hee] using hp

theorem probe_new (j : J) (hj : ¬IsMax j) (d : ProbeData M)
    (hd : schedule j = .inl d) (k : J) (hjk : Order.succ j ≤ k) :
    ¬ ∃ x : (functor M schedule).obj j,
      (functor M schedule).map (homOfLE ((Order.le_succ j).trans hjk)) x =
        probe M schedule j hj d hd k hjk := by
  rintro ⟨x,hx⟩
  rw [← inclusion_afterRequestMap M schedule j hj (.inl d) hd k hjk] at hx
  exact (d.map (fromBase M schedule j)).probe_new
    ⟨x,(afterRequestMap M schedule j hj (.inl d) hd k hjk).injective hx⟩

/-- Independence is with respect to the whole previous stage, not merely the
round's starting monoid. -/
theorem probe_independent (j : J) (hj : ¬IsMax j) (d : ProbeData M)
    (hd : schedule j = .inl d) (k : J) (hjk : Order.succ j ≤ k)
    (x : (functor M schedule).obj j)
    (hx : x ∣ (fromBase M schedule j d.a) * ((functor M schedule).obj j).e)
    (hxa : ¬ x ∣ fromBase M schedule j d.a) (z : (functor M schedule).obj k) :
    (functor M schedule).map (homOfLE ((Order.le_succ j).trans hjk)) x ∣ z ∧
      probe M schedule j hj d hd k hjk ∣ z ↔ fromBase M schedule k d.a * ((functor M schedule).obj k).e ∣ z := by
  let d' := d.map (fromBase M schedule j)
  let f : d'.extension ⟶ (functor M schedule).obj k :=
    afterRequestMap M schedule j hj (.inl d) hd k hjk
  have h := f.conservative.intersections _ _ _ (d'.independent x hx hxa) z
  have he := fromBase_afterRequestMap M schedule j hj (.inl d) hd k hjk d.a
  have htrans := inclusion_afterRequestMap M schedule j hj (.inl d) hd k hjk
  change d'.inclusion ≫ f = _ at htrans
  change f (d'.inclusion d'.a) = _ at he
  change ((d'.inclusion ≫ f) x ∣ z ∧ probe M schedule j hj d hd k hjk ∣ z) ↔
    f (d'.inclusion (d'.a * ((functor M schedule).obj j).e)) ∣ z at h
  simpa only [htrans,d'.inclusion.toMonoidHom.map_mul,f.toMonoidHom.map_mul,d'.inclusion.map_e,
    f.map_e,he] using h
end MonoidConstruction.Round
end
end PartitionConsistency


/-! ## CompleteRound -/
namespace PartitionConsistency.MonoidConstruction
universe u
open CategoryTheory CategoryTheory.Limits DiagramOrder
noncomputable section
open scoped Classical
namespace Round
variable {J : Type u} [CompleteLinearOrder J] [SuccOrder J] [WellFoundedLT J]
  (M : Object.{u}) (schedule : J → Request M)

theorem probes_ne_of_lt (i j : J) (hi : ¬IsMax i) (hj : ¬IsMax j)
    (di dj : ProbeData M) (hdi : schedule i = .inl di) (hdj : schedule j = .inl dj)
    (hij : i < j) (k : J) (hjk : Order.succ j ≤ k) :
    probe M schedule i hi di hdi k ((Order.succ_le_iff_of_not_isMax hi).2 hij |>.trans
      ((Order.le_succ j).trans hjk)) ≠ probe M schedule j hj dj hdj k hjk := by
  intro he
  let hle := (Order.succ_le_iff_of_not_isMax hi).2 hij
  apply probe_new M schedule j hj dj hdj k hjk
  refine ⟨probe M schedule i hi di hdi j hle,?_⟩
  rw [probe_transition]
  exact he

/-- Any two distinct executions of one datum have exactly the common exit cone. -/
theorem probes_independent_of_lt (i j : J) (hi : ¬IsMax i) (hj : ¬IsMax j)
    (d : ProbeData M) (hdi : schedule i = .inl d) (hdj : schedule j = .inl d)
    (hij : i < j) (k : J) (hjk : Order.succ j ≤ k) (z : (functor M schedule).obj k) :
    probe M schedule i hi d hdi k ((Order.succ_le_iff_of_not_isMax hi).2 hij |>.trans
      ((Order.le_succ j).trans hjk)) ∣ z ∧ probe M schedule j hj d hdj k hjk ∣ z ↔
      fromBase M schedule k d.a * ((functor M schedule).obj k).e ∣ z := by
  let hle := (Order.succ_le_iff_of_not_isMax hi).2 hij
  have hp := probe_profile M schedule i hi d hdi j hle
  have h : probe M schedule i hi d hdi j hle ∣
      fromBase M schedule j d.a * ((functor M schedule).obj j).e :=
    ⟨fromBase M schedule j d.b,hp.exit.symm⟩
  simpa only [probe_transition] using
    probe_independent M schedule j hj d hdj k hjk _ h hp.not_divides z
end Round

/- An entire round schedules every available datum, once for every repetition
index. Its chosen well-order is immaterial to conservation and independence. -/
namespace CompleteRound
variable (M : Object.{u}) (K : Type u) [Nonempty K]
abbrev Index := ScheduleIndex (Request M × K)

def schedule : Index M K → Request M
  | none => .inl (Request.defaultProbe M)
  | some d => d.1

def place (d : Request M) (i : K) : Index M K := some (d,i)
omit [Nonempty K] in
@[simp] theorem at_place (d : Request M) (i : K) : schedule M K (place M K d i) = d := rfl

theorem place_not_isMax (d : Request M) (i : K) : ¬IsMax (place M K d i) := by
  apply not_isMax_iff_ne_top.mpr
  exact WithTop.coe_ne_top

omit [Nonempty K] in
theorem place_injective (d : Request M) : Function.Injective (place M K d) := by
  intro i j h
  exact (Prod.mk.inj (Option.some.inj h)).2

abbrev tower : Index M K ⥤ Object.{u} := Round.functor M (schedule M K)
def target : Object.{u} := (tower M K).obj ⊤
def inclusion : M ⟶ target M K := Round.fromBase M (schedule M K) ⊤

theorem preservesProfiles : PreservesProfiles (inclusion M K) :=
  Round.fromBase_preservesProfiles M (schedule M K) ⊤

theorem cardinal_le {μ : Cardinal.{u}} (hω : Cardinal.aleph0 ≤ μ)
    (hpow : μ ^ Cardinal.aleph0 = μ) (hM : Cardinal.mk M ≤ μ) (hK : Cardinal.mk K ≤ μ) :
    Cardinal.mk (target M K) ≤ μ := by
  apply Round.cardinal_le M (schedule M K) hω _ hM
  change Cardinal.mk (Option (Request M × K)) ≤ μ
  simp only [Cardinal.mk_option,Cardinal.mk_prod,Cardinal.lift_id]
  exact (add_le_add ((mul_le_mul' (Request.data_cardinal_le hω hpow hM) hK).trans_eq
    (Cardinal.mul_eq_self hω)) (Cardinal.one_le_aleph0.trans hω)).trans_eq (Cardinal.add_eq_self hω)

def probe (d : ProbeData M) (i : K) : target M K :=
  Round.probe M (schedule M K) (place M K (.inl d) i) (place_not_isMax M K _ _) d rfl ⊤ le_top

theorem probe_profile (d : ProbeData M) (i : K) :
    ProbeProfile (inclusion M K d.a) (inclusion M K d.b) (target M K).e
      (probe M K d i) (fun j => inclusion M K (d.path.node j)) :=
  Round.probe_profile M (schedule M K) (place M K (.inl d) i) (place_not_isMax M K _ _) d rfl ⊤ le_top

theorem probe_injective (d : ProbeData M) : Function.Injective (probe M K d) := by
  intro i j he
  by_contra hij
  have hne := (place_injective M K (.inl d)).ne hij
  rcases lt_or_gt_of_ne hne with h | h
  · exact Round.probes_ne_of_lt M (schedule M K) _ _ (place_not_isMax M K _ _)
      (place_not_isMax M K _ _) d d rfl rfl h ⊤ le_top he
  · exact Round.probes_ne_of_lt M (schedule M K) _ _ (place_not_isMax M K _ _)
      (place_not_isMax M K _ _) d d rfl rfl h ⊤ le_top he.symm

theorem probes_independent (d : ProbeData M) (i j : K) (hij : i ≠ j) (z : target M K) :
    probe M K d i ∣ z ∧ probe M K d j ∣ z ↔ inclusion M K d.a * (target M K).e ∣ z := by
  have hne := (place_injective M K (.inl d)).ne hij
  rcases lt_or_gt_of_ne hne with h | h
  · exact Round.probes_independent_of_lt M (schedule M K) _ _ (place_not_isMax M K _ _)
      (place_not_isMax M K _ _) d rfl rfl h ⊤ le_top z
  · have h := Round.probes_independent_of_lt M (schedule M K) _ _ (place_not_isMax M K _ _)
      (place_not_isMax M K _ _) d rfl rfl h ⊤ le_top z
    exact and_comm.trans h

theorem realizes_merger (d : MergerData M) :
    ∃ l : Fin d.n → target M K, (d.prescription.map (inclusion M K).toMonoidHom).RootSystem l :=
  Round.creates_merger M (schedule M K) (place M K (.inr d) (Classical.choice ‹Nonempty K›))
    (place_not_isMax M K _ _) d rfl ⊤ le_top
end CompleteRound
end
end PartitionConsistency.MonoidConstruction


/-! ## OuterIteration -/

namespace PartitionConsistency.MonoidConstruction
universe u v
open CategoryTheory CategoryTheory.Limits DiagramOrder
noncomputable section
open scoped Classical

/-- The first uncountable ordinal, as a small indexing type. There is no
inaccessible-cardinal or chain-length closure assumption in this index. -/
abbrev RoundOrdinal : Type u := (Cardinal.aleph.{u} 1).ord.ToType
namespace RoundOrdinal
instance : Nonempty RoundOrdinal.{u} := Ordinal.nonempty_toType_iff.mpr
  Cardinal.isRegular_aleph_one.ord_pos.ne'
instance : OrderBot RoundOrdinal.{u} := WellFoundedLT.toOrderBot _
instance : ConditionallyCompleteLinearOrderBot RoundOrdinal.{u} :=
  WellFoundedLT.conditionallyCompleteLinearOrderBot _
instance : NoMaxOrder RoundOrdinal.{u} := Cardinal.noMaxOrder Cardinal.aleph0_lt_aleph_one.le

/-- Countably many round indices are bounded before the last union. -/
theorem countable_bounded {A : Type v} [Countable A] (f : A → RoundOrdinal.{u}) :
    ∃ j : RoundOrdinal.{u}, ∀ i, f i ≤ j := by
  let g : A → Ordinal.{u} := fun i => (f i).toOrd.val
  have hg : ∀ i, g i < (Cardinal.aleph.{u} 1).ord := fun i => (f i).toOrd.property
  have hc : Cardinal.lift.{u,v} (Cardinal.mk A) <
      (Ordinal.lift.{v,u} (Cardinal.aleph.{u} 1).ord).cof := by
    rw [← Ordinal.lift_cof, Cardinal.isRegular_aleph_one.cof_ord]
    have h : Cardinal.lift.{u,v} (Cardinal.mk A) ≤ Cardinal.aleph0 := by
      simpa only [Cardinal.lift_aleph0] using
        Cardinal.lift_le.mpr (Cardinal.mk_le_aleph0 (α := A))
    exact h.trans_lt (by simp)
  have hb := Ordinal.lift_iSup_lt_of_lt_cof hc hg
  let j : RoundOrdinal.{u} := Ordinal.ToType.mk ⟨iSup g,hb⟩
  refine ⟨j,fun i => ?_⟩
  apply Ordinal.ToType.mk.symm.le_iff_le.mp
  change (Ordinal.ToType.mk.symm (f i)).val ≤ (Ordinal.ToType.mk.symm j).val
  change g i ≤ (Ordinal.ToType.mk.symm (Ordinal.ToType.mk ⟨iSup g,hb⟩)).val
  simpa only [OrderIso.symm_apply_apply] using
    le_ciSup (show BddAbove (Set.range g) from ⟨_,fun _ ⟨i,hi⟩ => hi ▸ (hg i).le⟩) i

@[simp] theorem cardinal : Cardinal.mk RoundOrdinal.{u} = Cardinal.aleph 1 := by
  rw [RoundOrdinal,Cardinal.mk_toType,Cardinal.card_ord]
end RoundOrdinal

abbrev OuterIndex : Type u := WithTop RoundOrdinal.{u}
instance : SuccOrder OuterIndex.{u} := SuccOrder.ofLinearWellFoundedLT _

theorem outer_top_limit : Order.IsSuccLimit (⊤ : OuterIndex.{u}) := WithTop.isSuccLimit_top

theorem outer_countable_bound {A : Type v} [Countable A] (f : A → OuterIndex.{u})
    (hf : ∀ i, f i < ⊤) : ∃ j : OuterIndex.{u}, j < ⊤ ∧ ∀ i, f i ≤ j := by
  let g : A → RoundOrdinal.{u} := fun i => (f i).untop (ne_of_lt (hf i))
  obtain ⟨j,hj⟩ := RoundOrdinal.countable_bounded g
  refine ⟨j,WithTop.coe_lt_top j,fun i => ?_⟩
  rw [← WithTop.coe_untop (f i) (ne_of_lt (hf i))]
  exact WithTop.coe_le_coe.mpr (hj i)

namespace Saturation
variable (M : Object.{u}) (K : Type u) [Nonempty K]

def step (_ : OuterIndex.{u}) (X : Object.{u}) : ConstructionIteration.Step X :=
  ⟨CompleteRound.target X K, CompleteRound.inclusion X K⟩
abbrev tower : OuterIndex.{u} ⥤ Object.{u} := ConstructionIteration.functor M (step K)

def botIso : (tower M K).obj ⊥ ≅ M := ConstructionIteration.botIso M (step K)
def succIso (j : OuterIndex.{u}) (hj : j < ⊤) :
    (tower M K).obj (Order.succ j) ≅ CompleteRound.target ((tower M K).obj j) K :=
  ConstructionIteration.succIso M (step K) j (not_isMax_iff_ne_top.mpr hj.ne)

theorem map_succ (j : OuterIndex.{u}) (hj : j < ⊤) :
    (tower M K).map (homOfLE (Order.le_succ j)) =
      CompleteRound.inclusion ((tower M K).obj j) K ≫ (succIso M K j hj).inv :=
  ConstructionIteration.map_succ M (step K) j (not_isMax_iff_ne_top.mpr hj.ne)

def target : Object.{u} := (tower M K).obj ⊤
def fromStage (j : OuterIndex.{u}) : (tower M K).obj j ⟶ target M K :=
  (tower M K).map (homOfLE le_top)
def inclusion : M ⟶ target M K := (botIso M K).inv ≫ fromStage M K ⊥

theorem preservesProfiles (i j : OuterIndex.{u}) (hij : i ≤ j) :
    PreservesProfiles ((tower M K).map (homOfLE hij)) := by
  apply ContinuousTower.preservesProfiles
  intro k hk
  have hkt : k < ⊤ := lt_top_iff_ne_top.mpr (not_isMax_iff_ne_top.mp hk)
  rw [map_succ M K k hkt]
  exact (CompleteRound.preservesProfiles _ K).comp
    (PreservesProfiles.of_iso (succIso M K k hkt).symm)

theorem cardinal_le {μ : Cardinal.{u}} (hω : Cardinal.aleph 1 ≤ μ)
    (hpow : μ ^ Cardinal.aleph0 = μ) (hM : Cardinal.mk M ≤ μ) (hK : Cardinal.mk K ≤ μ)
    (j : OuterIndex.{u}) : Cardinal.mk ((tower M K).obj j) ≤ μ := by
  have hω₀ := Cardinal.aleph0_lt_aleph_one.le.trans hω
  apply ContinuousTower.cardinal_le _ hω₀
  · change Cardinal.mk (Option RoundOrdinal.{u}) ≤ μ
    rw [Cardinal.mk_option, RoundOrdinal.cardinal]
    exact (add_le_add hω (Cardinal.one_le_aleph0.trans hω₀)).trans_eq (Cardinal.add_eq_self hω₀)
  · rw [Cardinal.mk_congr (isoEquiv (botIso M K))]
    exact hM
  · intro k hk h
    have hkt : k < ⊤ := lt_top_iff_ne_top.mpr (not_isMax_iff_ne_top.mp hk)
    rw [Cardinal.mk_congr (isoEquiv (succIso M K k hkt))]
    exact CompleteRound.cardinal_le _ K hω₀ hpow h hK

/-- Every countable set of final elements, with no restriction on their
birth rounds, lies in one proper stage, before a following complete round. -/
theorem countable_stage {A : Type v} [Countable A] (f : A → target M K) :
    ∃ j : OuterIndex.{u}, j < ⊤ ∧ ∃ g : A → (tower M K).obj j,
      ∀ a, fromStage M K j (g a) = f a := by
  have h (a : A) := ContinuousTower.exists_rep (tower M K) outer_top_limit (f a)
  choose i hi x hx using h
  obtain ⟨j,hj,hij⟩ := outer_countable_bound i hi
  refine ⟨j,hj,fun a => (tower M K).map (homOfLE (hij a)) (x a),fun a => ?_⟩
  change (((tower M K).map (homOfLE (hij a))) ≫ fromStage M K j) (x a) = _
  unfold fromStage
  erw [← Functor.map_comp, homOfLE_comp]
  exact hx a

end Saturation
end
end PartitionConsistency.MonoidConstruction

end OAI
