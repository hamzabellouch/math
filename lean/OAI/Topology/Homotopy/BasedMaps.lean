import Mathlib

namespace OAI

/-! Maps of based generalized loops and homotopy groups. -/

noncomputable section
universe u v w


namespace NearbyLagrangian.BasedHomotopy
open scoped Topology Topology.Homotopy
variable {N X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
variable {x : X} {y : Y} {z : Z}

def loopMap (e : C(X,Y)) (he : e x = y) (f : GenLoop N X x) : GenLoop N Y y :=
  ⟨e.comp f.1,fun t ht => (congrArg e (GenLoop.boundary f t ht)).trans he⟩

lemma loopMap_homotopic (e : C(X,Y)) (he : e x = y) {f g : GenLoop N X x}
    (h : GenLoop.Homotopic f g) : GenLoop.Homotopic (loopMap e he f) (loopMap e he g) := by
  obtain ⟨H⟩ := h
  exact ⟨H.compContinuousMap e⟩

@[simp] theorem loopMap_const (e : C(X,Y)) (he : e x = y) :
    loopMap (N:=N) e he GenLoop.const = GenLoop.const := by ext t; exact he

@[simp] theorem loopMap_id (f : GenLoop N X x) : loopMap (ContinuousMap.id X) rfl f = f := by
  ext t; rfl

@[simp] theorem loopMap_comp (e : C(X,Y)) (he : e x = y) (d : C(Y,Z)) (hd : d y = z)
    (f : GenLoop N X x) : loopMap d hd (loopMap e he f) =
      loopMap (d.comp e) ((congrArg d he).trans hd) f := by
  ext t; rfl

lemma loopMap_transAt [DecidableEq N] (e : C(X,Y)) (he : e x = y)
    (i : N) (f g : GenLoop N X x) : loopMap e he (GenLoop.transAt i f g) =
      GenLoop.transAt i (loopMap e he f) (loopMap e he g) := by
  ext t
  simp only [loopMap,GenLoop.mk_apply,ContinuousMap.comp_apply,GenLoop.transAt,GenLoop.coe_copy,GenLoop.coe_coe]
  split_ifs <;> rfl

def groupMap [DecidableEq N] [Nonempty N] (e : C(X,Y)) (he : e x = y) :
    HomotopyGroup N X x →* HomotopyGroup N Y y where
  toFun := Quotient.map (loopMap e he) (fun _ _ h => loopMap_homotopic e he h)
  map_one' := by
    rw [HomotopyGroup.one_def,HomotopyGroup.one_def]
    change Quotient.mk'' (loopMap e he GenLoop.const) = Quotient.mk'' GenLoop.const
    rw [loopMap_const]
  map_mul' a b := Quotient.inductionOn₂ a b fun f g => by
    simp only [HomotopyGroup.mul_spec (i:=Classical.arbitrary N)]
    change (⟦loopMap e he (GenLoop.transAt (Classical.arbitrary N) g f)⟧ : HomotopyGroup N Y y) =
      ((· * ·) : HomotopyGroup N Y y → HomotopyGroup N Y y → HomotopyGroup N Y y)
        ⟦loopMap e he f⟧ ⟦loopMap e he g⟧
    rw [HomotopyGroup.mul_spec (i:=Classical.arbitrary N),loopMap_transAt]

@[simp] theorem groupMap_id [DecidableEq N] [Nonempty N] (a : HomotopyGroup N X x) :
    groupMap (ContinuousMap.id X) rfl a = a := by
  induction a using Quotient.inductionOn with
  | h f => change Quotient.mk'' (loopMap _ _ f) = _; rw [loopMap_id]; rfl

@[simp] theorem groupMap_comp [DecidableEq N] [Nonempty N]
    (e : C(X,Y)) (he : e x = y) (d : C(Y,Z)) (hd : d y = z) (a : HomotopyGroup N X x) :
    groupMap d hd (groupMap e he a) = groupMap (d.comp e) ((congrArg d he).trans hd) a := by
  induction a using Quotient.inductionOn with
  | h f => change Quotient.mk'' (loopMap _ _ (loopMap _ _ f)) = _; rw [loopMap_comp]; rfl

end NearbyLagrangian.BasedHomotopy

end

end OAI
