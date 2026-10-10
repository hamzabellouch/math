import OAI.RingTheory.BassTrace.PathComplex

namespace OAI

noncomputable section

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral

namespace BassTrace.Detector

section

variable {G : Type*} [Group G]

lemma SubtypeCentralizer_commutes (g : G) (c : Subgroup.centralizer ({g} : Set G)) :
    Commute g (c : G) := (Subgroup.mem_centralizer_singleton_iff.mp c.property).symm

abbrev Centralizer (g : G) := Subgroup.centralizer ({g} : Set G)

def generator (g : G) : Centralizer g :=
  ⟨g, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

@[simp] lemma generator_coe (g : G) : (generator g : G) = g := rfl

lemma generator_commutes (g : G) (c : Centralizer g) : Commute (generator g) c := by
  apply Subtype.ext
  exact (SubtypeCentralizer_commutes g c).eq

def cyclic (g : G) : Subgroup (Centralizer g) := Subgroup.zpowers (generator g)

instance cyclic_normal (g : G) : (cyclic g).Normal where
  conj_mem a ha c := by
    obtain ⟨r,rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hc := (generator_commutes g c).zpow_left r
    rw [← hc.eq,mul_inv_cancel_right]
    exact (Subgroup.zpowers (generator g)).zpow_mem (Subgroup.mem_zpowers _) r

abbrev ActingGroup (g : G) := Centralizer g ⧸ cyclic g

def centralizerPerm (g : G) : Centralizer g →* Equiv.Perm (Vertex g) where
  toFun c := {
    toFun := centralizerAct g c
    invFun := centralizerAct g c⁻¹
    left_inv y := by rw [← centralizerAct_mul,inv_mul_cancel,centralizerAct_one]
    right_inv y := by rw [← centralizerAct_mul,mul_inv_cancel,centralizerAct_one] }
  map_one' := Equiv.ext (centralizerAct_one g)
  map_mul' c d := Equiv.ext (centralizerAct_mul g c d)

lemma cyclic_le_ker (g : G) : cyclic g ≤ (centralizerPerm g).ker := by
  rintro c hc
  obtain ⟨r,rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
  apply Equiv.ext
  intro y
  induction y using Quotient.inductionOn with | _ h =>
    change project g (g^r*h) = project g h
    apply (project_eq_iff g _ _).mpr
    refine ⟨-r, ?_⟩
    simp [← mul_assoc]

def quotientPerm (g : G) : ActingGroup g →* Equiv.Perm (Vertex g) :=
  QuotientGroup.lift (cyclic g) (centralizerPerm g) (cyclic_le_ker g)

instance vertexAction (g : G) : MulAction (ActingGroup g) (Vertex g) :=
  MulAction.compHom (Vertex g) (quotientPerm g)

@[simp] lemma quotient_smul_project (g : G) (c : Centralizer g) (h : G) :
    (QuotientGroup.mk c : ActingGroup g) • project g h = project g (c*h) := rfl

lemma vertex_action_free (g : G) (a : ActingGroup g) (y : Vertex g)
    (ha : a • y = y) : a = 1 := by
  induction a using Quotient.inductionOn with | _ c =>
    induction y using Quotient.inductionOn with | _ h =>
      apply (QuotientGroup.eq_one_iff c).mpr
      change project g ((c:G)*h) = project g h at ha
      obtain ⟨r,hr⟩ := (project_eq_iff g _ _).mp ha
      have he : g^r*(c:G) = 1 := by
        apply mul_right_cancel (b := h)
        simpa only [mul_assoc,one_mul] using hr
      have hc : c = (generator g)^(-r) := by
        apply Subtype.ext
        change (c:G) = g^(-r)
        rw [zpow_neg]
        exact eq_inv_of_mul_eq_one_right he
      rw [hc]
      exact (cyclic g).zpow_mem (Subgroup.mem_zpowers _) _

lemma actingGroup_injective_orbit (g : G) (y : Vertex g) :
    Function.Injective (fun a : ActingGroup g => a • y) := by
  intro a b hab
  change a • y = b • y at hab
  have hh : (b⁻¹*a) • y = y := by rw [mul_smul,hab,inv_smul_smul]
  exact (inv_mul_eq_one.mp (vertex_action_free g _ y hh)).symm

end

open Set Finset

variable {G : Type*} [Group G]

def rightMul (g s : G) : Vertex g → Vertex g :=
  Quotient.map' (fun h => h*s) (by
    intro h k hk
    obtain ⟨r,hr⟩ := (project_eq_iff g h k).mp (Quotient.sound hk)
    apply Quotient.exact
    apply (project_eq_iff g _ _).mpr
    exact ⟨r,by rw [← mul_assoc,hr]⟩)

@[simp] lemma rightMul_project (g s h : G) : rightMul g s (project g h) = project g (h*s) := rfl

@[simp] lemma rightMul_one (g : G) (y : Vertex g) : rightMul g 1 y = y := by
  induction y using Quotient.inductionOn with | _ h =>
    change project g (h*1) = project g h
    rw [mul_one]

lemma rightMul_mul (g s t : G) (y : Vertex g) :
    rightMul g (s*t) y = rightMul g t (rightMul g s y) := by
  induction y using Quotient.inductionOn with | _ h =>
    change project g (h*(s*t)) = project g ((h*s)*t)
    rw [mul_assoc]

lemma smul_rightMul (g : G) (a : ActingGroup g) (s : G) (y : Vertex g) :
    a • rightMul g s y = rightMul g s (a • y) := by
  induction a using Quotient.inductionOn with | _ c =>
    induction y using Quotient.inductionOn with | _ h =>
      change project g ((c:G)*(h*s)) = project g (((c:G)*h)*s)
      rw [mul_assoc]

def supportGraph (g : G) (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S) : SimpleGraph (Vertex g) where
  Adj y z := y ≠ z ∧ ∃ s ∈ S, rightMul g s y = z
  symm := ⟨by
    rintro y z ⟨hne,s,hs,rfl⟩
    refine ⟨hne.symm,s⁻¹,hS s hs,?_⟩
    rw [← rightMul_mul,mul_inv_cancel,rightMul_one]⟩
  loopless := ⟨by rintro y ⟨h,_⟩; exact h rfl⟩

lemma supportGraph_adj (g : G) (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S) (y z : Vertex g) :
    (supportGraph g S hS).Adj y z ↔ y ≠ z ∧ ∃ s ∈ S, rightMul g s y = z := Iff.rfl

lemma supportGraph_smul (g : G) (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (a : ActingGroup g) (y z : Vertex g) :
    (supportGraph g S hS).Adj (a • y) (a • z) ↔ (supportGraph g S hS).Adj y z := by
  simp only [supportGraph_adj,Ne,smul_left_cancel_iff]
  constructor
  · rintro ⟨hne,s,hs,he⟩
    exact ⟨hne,s,hs,(MulAction.injective a) (by change a • rightMul g s y = a • z; rw [smul_rightMul]; exact he)⟩
  · rintro ⟨hne,s,hs,he⟩
    exact ⟨hne,s,hs,by rw [← smul_rightMul,he]⟩

lemma supportGraph_finite_neighbors (g : G) (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (y : Vertex g) : ((supportGraph g S hS).neighborSet y).Finite := by
  classical
  apply (S.image (fun s => rightMul g s y)).finite_toSet.subset
  rintro z ⟨_,s,hs,rfl⟩
  exact Finset.mem_image_of_mem _ hs

scoped instance supportGraphLocallyFinite (g : G) (S : Finset G)
    (hS : ∀ s ∈ S, s⁻¹ ∈ S) : (supportGraph g S hS).LocallyFinite :=
  fun y => (supportGraph_finite_neighbors g S hS y).fintype

open scoped BassTrace.Detector

lemma supportGraph_degree_le (g : G) (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (y : Vertex g) : (supportGraph g S hS).degree y ≤ S.card := by
  classical
  calc (supportGraph g S hS).degree y = ((supportGraph g S hS).neighborFinset y).card := rfl
    _ ≤ (S.image (fun s => rightMul g s y)).card := Finset.card_le_card (by
      intro z hz
      obtain ⟨_,s,hs,rfl⟩ := (SimpleGraph.mem_neighborFinset _ _ _).mp hz
      exact Finset.mem_image_of_mem _ hs)
    _ ≤ S.card := Finset.card_image_le

lemma supportGraph_reachable_rightMul (g : G) (S : Finset G)
    (hS : ∀ s ∈ S, s⁻¹ ∈ S) (s : G) (hs : s ∈ Subgroup.closure (S : Set G)) :
    ∀ y, (supportGraph g S hS).Reachable y (rightMul g s y) := by
  induction hs using Subgroup.closure_induction with
  | mem s hs =>
    intro y
    by_cases he : y = rightMul g s y
    · rw [← he]
    · exact (show (supportGraph g S hS).Adj y (rightMul g s y) from ⟨he,s,hs,rfl⟩).reachable
  | one => intro y; rw [rightMul_one]
  | mul a b ha hb ia ib =>
    intro y
    rw [rightMul_mul]
    exact (ia y).trans (ib (rightMul g a y))
  | inv a ha ia =>
    intro y
    have h := (ia (rightMul g a⁻¹ y)).symm
    simpa [← rightMul_mul] using h

lemma supportGraph_connected (g : G) (S : Finset G)
    (hS : ∀ s ∈ S, s⁻¹ ∈ S) (hgen : Subgroup.closure (S : Set G) = ⊤) :
    (supportGraph g S hS).Connected := by
  have : Nonempty (Vertex g) := ⟨project g 1⟩
  refine ⟨?_⟩
  intro y z
  induction y using Quotient.inductionOn with | _ a =>
    induction z using Quotient.inductionOn with | _ b =>
      have h := supportGraph_reachable_rightMul g S hS (a⁻¹*b) (by rw [hgen]; trivial) (project g a)
      change (supportGraph g S hS).Reachable (project g a) (project g b)
      simpa [mul_assoc] using h

scoped instance vertexIsCancelSMul (g : G) : IsCancelSMul (ActingGroup g) (Vertex g) where
  left_cancel' a _ _ he := (MulAction.injective a) he
  right_cancel' _ _ x he := (actingGroup_injective_orbit g x) he

end BassTrace.Detector

end

end OAI
