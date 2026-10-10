import OAI.SetTheory.PartitionPrinciple.Definability.BoundedMeetOrderCodes
import OAI.SetTheory.PartitionPrinciple.Definability.GroundPowerImageGraphs
import OAI.SetTheory.PartitionPrinciple.Definability.StrictLexHeightFormulas

namespace OAI

namespace PartitionPilot.Forcing
open SetFormula
universe u

structure MainStageLaws (P r μ G m inv one A b t height C D rD : ZFSet.{u}) : Prop where
  meet : MeetOrderCode P r μ
  group : GroupCode G m inv one
  action : PosetActionCode G P m one r A
  bottom_mem : b ∈ P
  least : ∀ x ∈ P, ZFSet.pair b x ∈ r
  top_mem : t ∈ P
  greatest : ∀ x ∈ P, ZFSet.pair x t ∈ r
  height_code : StrictLexHeightCode P C D r height rD

def MainStageValidity (M : TransitiveGround.{u})
    (P r μ G m inv one A b t height C D rD : ZFSet.{u}) : Prop :=
  MainStageLaws P r μ G m inv one A b t height C D rD ∧
    M.groundEmbeddable (relationImage P (ZFSet.prod C D) height) ZFSet.omega

namespace BoundedFormula

def bottomFormula {n} (P r b : Fin n) : BoundedFormula n :=
  .conj (.mem b P) (.allMem P (pairMembershipFormula b.succ 0 r.succ))

theorem truth_bottomFormula {n} (P r b : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (bottomFormula P r b) env ↔
      env b ∈ env P ∧ ∀ x ∈ env P, ZFSet.pair (env b) x ∈ env r := by
  simp only [bottomFormula, Truth, truth_pairMembershipFormula]
  rfl

def productEquationFormula {n} (B C D : Fin n) : BoundedFormula n :=
  .conj (.allMem B (productElementFormula 0 C.succ D.succ))
    (.allMem C (.allMem D.succ (pairMembershipFormula 1 0 B.succ.succ)))

theorem truth_productEquationFormula {n} (B C D : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (productEquationFormula B C D) env ↔ env B = ZFSet.prod (env C) (env D) := by
  simp only [productEquationFormula, Truth, truth_productElementFormula,
    truth_pairMembershipFormula]
  change ((∀ z ∈ env B, z ∈ ZFSet.prod (env C) (env D)) ∧
    ∀ c ∈ env C, ∀ d ∈ env D, ZFSet.pair c d ∈ env B) ↔ _
  constructor
  · rintro ⟨subset, covers⟩
    apply ZFSet.ext
    intro z
    refine ⟨subset z, ?_⟩
    rintro hz
    obtain ⟨c, hc, d, hd, rfl⟩ := ZFSet.mem_prod.1 hz
    exact covers c hc d hd
  · rintro equal
    rw [equal]
    exact ⟨fun _ h => h, fun _ hc _ hd => ZFSet.pair_mem_prod.2 ⟨hc, hd⟩⟩

def mainStageLawsFormula {n} (P r μ G m inv one A b t height C D rD : Fin n) :
    BoundedFormula n :=
  .conj (meetOrderFormula P r μ) (.conj (groupFormula G m inv one)
    (.conj (posetActionFormula G P m one r A) (.conj (bottomFormula P r b)
      (.conj (topFormula P r t) (strictLexHeightFormula P C D r height rD)))))

theorem truth_mainStageLawsFormula {n}
    (P r μ G m inv one A b t height C D rD : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (mainStageLawsFormula P r μ G m inv one A b t height C D rD) env ↔
      MainStageLaws (env P) (env r) (env μ) (env G) (env m) (env inv) (env one)
        (env A) (env b) (env t) (env height) (env C) (env D) (env rD) := by
  simp only [mainStageLawsFormula, Truth, truth_meetOrderFormula, truth_groupFormula,
    truth_posetActionFormula, truth_bottomFormula, truth_topFormula, truth_strictLexHeightFormula]
  exact ⟨fun ⟨meet, group, action, ⟨hb, least⟩, ⟨ht, greatest⟩, height⟩ =>
    ⟨meet, group, action, hb, least, ht, greatest, height⟩,
    fun h => ⟨h.meet, h.group, h.action, ⟨h.bottom_mem, h.least⟩,
      ⟨h.top_mem, h.greatest⟩, h.height_code⟩⟩

def mainStageWitnessFormula {n}
    (P r μ G m inv one A b t height C D rD B R N f : Fin n) : BoundedFormula n :=
  .conj (mainStageLawsFormula P r μ G m inv one A b t height C D rD)
    (.conj (productEquationFormula B C D)
      (.conj (imageSetFormula R P B height) (injectionFormula R N f)))

theorem truth_mainStageWitnessFormula {n}
    (P r μ G m inv one A b t height C D rD B R N f : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (mainStageWitnessFormula P r μ G m inv one A b t height C D rD B R N f) env ↔
      MainStageLaws (env P) (env r) (env μ) (env G) (env m) (env inv) (env one)
        (env A) (env b) (env t) (env height) (env C) (env D) (env rD) ∧
      env B = ZFSet.prod (env C) (env D) ∧
      env R = relationImage (env P) (env B) (env height) ∧
      InjectionCode (env R) (env N) (env f) := by
  simp only [mainStageWitnessFormula, Truth, truth_mainStageLawsFormula,
    truth_productEquationFormula, truth_imageSetFormula, truth_injectionFormula]

theorem realize_mainStageWitnessFormula (M : TransitiveGround.{u}) {n}
    (P r μ G m inv one A b t height C D rD B R N f : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets
      (mainStageWitnessFormula P r μ G m inv one A b t height C D rD B R N f).toFormula env ↔
      MainStageLaws (env P) (env r) (env μ) (env G) (env m) (env inv) (env one)
        (env A) (env b) (env t) (env height) (env C) (env D) (env rD) ∧
      env B = ZFSet.prod (env C) (env D) ∧
      env R = relationImage (env P) (env B) (env height) ∧
      InjectionCode (env R) (env N) (env f) :=
  (realize_toFormula M _ env members).trans
    (truth_mainStageWitnessFormula P r μ G m inv one A b t height C D rD B R N f env)

end BoundedFormula

namespace SetFormula

def mainStageValidityFormula {n}
    (P r μ G m inv one A b t height C D rD N : Fin n) : SetFormula n :=
  let lift (i : Fin n) := i.succ.succ.succ
  ex (ex (ex ((BoundedFormula.mainStageWitnessFormula
    (lift P) (lift r) (lift μ) (lift G) (lift m) (lift inv) (lift one)
    (lift A) (lift b) (lift t) (lift height) (lift C) (lift D) (lift rD)
    2 1 (lift N) 0).toFormula)))

def validMainStageCodeFormula {n}
    (z P r μ G m inv one A b t height C D rD N : Fin n) : SetFormula n :=
  .conj (BoundedFormula.mainStageFormula z P r μ G m inv one A b t height).toFormula
    (mainStageValidityFormula P r μ G m inv one A b t height C D rD N)

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
  (unions : Realize M.sets SetFormula.union Fin.elim0)
  (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem realize_mainStageValidityFormula {n}
    (P r μ G m inv one A b t height C D rD N : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) (omega : env N = ZFSet.omega) :
    Realize M.sets (mainStageValidityFormula P r μ G m inv one A b t height C D rD N) env ↔
      MainStageValidity M (env P) (env r) (env μ) (env G) (env m) (env inv) (env one)
        (env A) (env b) (env t) (env height) (env C) (env D) (env rD) := by
  simp only [mainStageValidityFormula, realize_ex]
  constructor
  · rintro ⟨B, hB, R, hR, f, hf, realized⟩
    have code := (BoundedFormula.realize_mainStageWitnessFormula M
      P.succ.succ.succ r.succ.succ.succ μ.succ.succ.succ G.succ.succ.succ
      m.succ.succ.succ inv.succ.succ.succ one.succ.succ.succ A.succ.succ.succ
      b.succ.succ.succ t.succ.succ.succ height.succ.succ.succ C.succ.succ.succ
      D.succ.succ.succ rD.succ.succ.succ 2 1 N.succ.succ.succ 0
      (extend f (extend R (extend B env)))
      (Fin.cases hf (Fin.cases hR (Fin.cases hB members)))).1 realized
    change MainStageLaws (env P) (env r) (env μ) (env G) (env m) (env inv) (env one)
      (env A) (env b) (env t) (env height) (env C) (env D) (env rD) ∧
      B = ZFSet.prod (env C) (env D) ∧
      R = relationImage (env P) B (env height) ∧ InjectionCode R (env N) f at code
    obtain ⟨laws, rfl, rfl, injection⟩ := code
    rw [omega] at injection
    exact ⟨laws, f, hf, injection⟩
  · rintro ⟨laws, f, hf, injection⟩
    let B := ZFSet.prod (env C) (env D)
    let R := relationImage (env P) B (env height)
    have hB : B ∈ M.sets := M.prod_mem pairing unions powers separation (members C) (members D)
    have hR : R ∈ M.sets := M.relationImage_mem separation (members P) hB (members height)
    refine ⟨B, hB, R, hR, f, hf, ?_⟩
    apply (BoundedFormula.realize_mainStageWitnessFormula M
      P.succ.succ.succ r.succ.succ.succ μ.succ.succ.succ G.succ.succ.succ
      m.succ.succ.succ inv.succ.succ.succ one.succ.succ.succ A.succ.succ.succ
      b.succ.succ.succ t.succ.succ.succ height.succ.succ.succ C.succ.succ.succ
      D.succ.succ.succ rD.succ.succ.succ 2 1 N.succ.succ.succ 0
      (extend f (extend R (extend B env)))
      (Fin.cases hf (Fin.cases hR (Fin.cases hB members)))).2
    refine ⟨laws, rfl, rfl, ?_⟩
    change InjectionCode R (env N) f
    rw [omega]
    exact injection

theorem realize_validMainStageCodeFormula {n}
    (z P r μ G m inv one A b t height C D rD N : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) (omega : env N = ZFSet.omega) :
    Realize M.sets (validMainStageCodeFormula z P r μ G m inv one A b t height C D rD N) env ↔
      env z = mainStageCode (env P) (env r) (env μ) (env G) (env m) (env inv) (env one)
        (env A) (env b) (env t) (env height) ∧
      MainStageValidity M (env P) (env r) (env μ) (env G) (env m) (env inv) (env one)
        (env A) (env b) (env t) (env height) (env C) (env D) (env rD) :=
  and_congr (BoundedFormula.realize_mainStageFormula M z P r μ G m inv one A b t height env members)
    (M.realize_mainStageValidityFormula pairing unions powers separation
      P r μ G m inv one A b t height C D rD N env members omega)

end TransitiveGround

namespace GroundMainStage
variable {M : TransitiveGround.{u}}

theorem validity {C D rD : ZFSet.{u}} (stage : GroundMainStage M C D rD) :
    MainStageValidity M stage.carrier stage.order stage.meetGraph stage.actors
      stage.multiplication stage.inverse stage.identity stage.action stage.bottom stage.top
      stage.height C D rD :=
  ⟨⟨stage.meet, stage.group_code, stage.action_code, stage.bottom_mem, stage.least,
    stage.top_mem, stage.greatest, stage.height_code⟩, stage.height_range_countable⟩

noncomputable def ofValidity
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P r μ G m inv one A b t height C D rD : ZFSet.{u}}
    (hP : P ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets) (hG : G ∈ M.sets)
    (hm : m ∈ M.sets) (hInv : inv ∈ M.sets) (hA : A ∈ M.sets) (hHeight : height ∈ M.sets)
    (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets)
    (valid : MainStageValidity M P r μ G m inv one A b t height C D rD) :
    GroundMainStage M C D rD :=
  ofCodes pairing unions powers separation hP hG hr hμ hA hm hInv hC hD hrD hHeight
    valid.1.meet valid.1.group valid.1.action valid.1.bottom_mem valid.1.least
    valid.1.top_mem valid.1.greatest valid.1.height_code valid.2

theorem ofValidity_code
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P r μ G m inv one A b t height C D rD : ZFSet.{u}}
    (hP : P ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets) (hG : G ∈ M.sets)
    (hm : m ∈ M.sets) (hInv : inv ∈ M.sets) (hA : A ∈ M.sets) (hHeight : height ∈ M.sets)
    (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets)
    (valid : MainStageValidity M P r μ G m inv one A b t height C D rD) :
    (ofValidity pairing unions powers separation hP hr hμ hG hm hInv hA hHeight hC hD hrD valid).code =
      mainStageCode P r μ G m inv one A b t height := rfl

end GroundMainStage

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem exists_mainStage_of_realize
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets) {n}
    (z P r μ G m inv one A b t height C D rD N : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) (omega : env N = ZFSet.omega)
    (recognized : Realize M.sets
      (validMainStageCodeFormula z P r μ G m inv one A b t height C D rD N) env) :
    ∃ stage : GroundMainStage M (env C) (env D) (env rD), stage.code = env z := by
  obtain ⟨encoded, valid⟩ := (M.realize_validMainStageCodeFormula pairing unions powers separation
    z P r μ G m inv one A b t height C D rD N env members omega).1 recognized
  refine ⟨GroundMainStage.ofValidity pairing unions powers separation (members P) (members r)
    (members μ) (members G) (members m) (members inv) (members A) (members height)
    (members C) (members D) (members rD) valid, ?_⟩
  exact encoded.symm

end TransitiveGround

namespace SetFormula

def mainStageCandidateFormula {n} (z C D rD N : Fin n) : SetFormula n :=
  let lift (i : Fin n) := i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  ex (ex (ex (ex (ex (ex (ex (ex (ex (ex (ex (validMainStageCodeFormula (lift z) 10 9 8 7 6 5 4 3 2 1 0
    (lift C) (lift D) (lift rD) (lift N))))))))))))

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_mainStageCandidateFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets) {n}
    (z C D rD N : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) (omega : env N = ZFSet.omega) :
    Realize M.sets (mainStageCandidateFormula z C D rD N) env ↔
      ∃ stage : GroundMainStage M (env C) (env D) (env rD), stage.code = env z := by
  simp only [mainStageCandidateFormula, realize_ex]
  constructor
  · rintro ⟨P, hP, r, hr, μ, hμ, G, hG, m, hm, inv, hInv, one, hOne, A, hA, b, hb, t, ht, height, hHeight, recognized⟩
    exact M.exists_mainStage_of_realize pairing unions powers separation
      z.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 10 9 8 7 6 5 4 3 2 1 0
      C.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ rD.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ N.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
      (extend height (extend t (extend b (extend A (extend one (extend inv (extend m (extend G (extend μ (extend r (extend P (env))))))))))))
      (Fin.cases hHeight (Fin.cases ht (Fin.cases hb (Fin.cases hA (Fin.cases hOne (Fin.cases hInv (Fin.cases hm (Fin.cases hG (Fin.cases hμ (Fin.cases hr (Fin.cases hP (members)))))))))))) omega recognized
  · rintro ⟨stage, equal⟩
    refine ⟨stage.carrier, stage.carrier_ground, stage.order, stage.order_ground, stage.meetGraph, stage.meet_ground, stage.actors, stage.actors_ground, stage.multiplication, stage.multiplication_ground, stage.inverse, stage.inverse_ground, stage.identity, stage.identity_ground, stage.action, stage.action_ground, stage.bottom, stage.bottom_ground, stage.top, stage.top_ground, stage.height, stage.height_ground, ?_⟩
    apply (M.realize_validMainStageCodeFormula pairing unions powers separation
      z.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 10 9 8 7 6 5 4 3 2 1 0
      C.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ rD.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ N.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
      (extend stage.height (extend stage.top (extend stage.bottom (extend stage.action (extend stage.identity (extend stage.inverse (extend stage.multiplication (extend stage.actors (extend stage.meetGraph (extend stage.order (extend stage.carrier (env))))))))))))
      (Fin.cases stage.height_ground (Fin.cases stage.top_ground (Fin.cases stage.bottom_ground (Fin.cases stage.action_ground (Fin.cases stage.identity_ground (Fin.cases stage.inverse_ground (Fin.cases stage.multiplication_ground (Fin.cases stage.actors_ground (Fin.cases stage.meet_ground (Fin.cases stage.order_ground (Fin.cases stage.carrier_ground (members)))))))))))) omega).2
    exact ⟨equal.symm, stage.validity⟩

noncomputable def mainStageCandidates (V C D rD : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ stage : GroundMainStage M C D rD, stage.code = z) V

theorem mem_mainStageCandidates (V C D rD z : ZFSet.{u}) :
    z ∈ M.mainStageCandidates V C D rD ↔
      z ∈ V ∧ ∃ stage : GroundMainStage M C D rD, stage.code = z := by
  rw [mainStageCandidates, ZFSet.mem_sep]

theorem mainStageCandidates_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {V C D rD : ZFSet.{u}} (hV : V ∈ M.sets) (hC : C ∈ M.sets)
    (hD : D ∈ M.sets) (hrD : rD ∈ M.sets) :
    M.mainStageCandidates V C D rD ∈ M.sets := by
  let params := extend C (extend D (extend rD (extend ZFSet.omega Fin.elim0)))
  have members : ∀ i, params i ∈ M.sets :=
    Fin.cases hC (Fin.cases hD (Fin.cases hrD
      (Fin.cases (M.omega_mem separation infinite) (fun i => Fin.elim0 i))))
  have selected := M.separation_mem separation (mainStageCandidateFormula 0 1 2 3 4)
    params members hV
  have equal : ZFSet.sep (fun z => Realize M.sets (mainStageCandidateFormula 0 1 2 3 4)
      (extend z params)) V = M.mainStageCandidates V C D rD := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, M.mem_mainStageCandidates]
    apply and_congr_right
    intro hz
    exact M.realize_mainStageCandidateFormula pairing unions powers separation 0 1 2 3 4
      (extend z params) (Fin.cases (M.transitive hV hz) members) rfl
  exact equal ▸ selected

theorem mainStage_code_mem_candidates {V C D rD : ZFSet.{u}}
    (stage : GroundMainStage M C D rD) (bound : stage.code ∈ V) :
    stage.code ∈ M.mainStageCandidates V C D rD :=
  (M.mem_mainStageCandidates V C D rD stage.code).2 ⟨bound, stage, rfl⟩

end TransitiveGround
end PartitionPilot.Forcing

end OAI
