import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.GeneratorPlacement

namespace OAI

namespace HarmonicArtin.ReversibleQuiver

variable {V A W B : Type*} (Q : ReversibleQuiver V A) (R : ReversibleQuiver W B)

structure Iso where
  vertex : V ≃ W
  arrow : A ≃ B
  source : ∀ a, R.source (arrow a) = vertex (Q.source a)
  target : ∀ a, R.target (arrow a) = vertex (Q.target a)
  reverse : ∀ a, R.reverse (arrow a) = arrow (Q.reverse a)

namespace Iso
variable {Q R} (e : Iso Q R)

@[simp] lemma source_symm (b:B) : Q.source (e.arrow.symm b) = e.vertex.symm (R.source b) := by
  apply e.vertex.injective
  simpa only [Equiv.apply_symm_apply] using (e.source (e.arrow.symm b)).symm

@[simp] lemma target_symm (b:B) : Q.target (e.arrow.symm b) = e.vertex.symm (R.target b) := by
  apply e.vertex.injective
  simpa only [Equiv.apply_symm_apply] using (e.target (e.arrow.symm b)).symm

@[simp] lemma reverse_symm (b:B) : Q.reverse (e.arrow.symm b) = e.arrow.symm (R.reverse b) := by
  apply e.arrow.injective
  simpa only [Equiv.apply_symm_apply] using (e.reverse (e.arrow.symm b)).symm

def refl (Q : ReversibleQuiver V A) : Iso Q Q where
  vertex := Equiv.refl V
  arrow := Equiv.refl A
  source _ := rfl
  target _ := rfl
  reverse _ := rfl

def symm : Iso R Q where
  vertex := e.vertex.symm
  arrow := e.arrow.symm
  source := e.source_symm
  target := e.target_symm
  reverse := e.reverse_symm

def trans {X C : Type*} {U : ReversibleQuiver X C} (f : Iso R U) : Iso Q U where
  vertex := e.vertex.trans f.vertex
  arrow := e.arrow.trans f.arrow
  source a := by dsimp; rw [f.source,e.source]
  target a := by dsimp; rw [f.target,e.target]
  reverse a := by dsimp; rw [f.reverse,e.reverse]

variable {K : Type*} [Field K] [Fintype A] [Fintype B] [DecidableEq V] [DecidableEq W]

noncomputable def zigzagLinear : Q.Zigzag K ≃ₗ[K] R.Zigzag K where
  toFun x := (x.vertex ∘ e.vertex.symm, x.arrow ∘ e.arrow.symm, x.token ∘ e.vertex.symm)
  invFun x := (x.vertex ∘ e.vertex, x.arrow ∘ e.arrow, x.token ∘ e.vertex)
  left_inv x := by apply Zigzag.ext <;> ext y <;> simp [Function.comp_def,Zigzag.vertex,Zigzag.arrow,Zigzag.token]
  right_inv x := by apply Zigzag.ext <;> ext y <;> simp [Function.comp_def,Zigzag.vertex,Zigzag.arrow,Zigzag.token]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma zigzagLinear_vertex (x : Q.Zigzag K) (v : W) :
    (e.zigzagLinear x).vertex v = x.vertex (e.vertex.symm v) := rfl
@[simp] lemma zigzagLinear_arrow (x : Q.Zigzag K) (b : B) :
    (e.zigzagLinear x).arrow b = x.arrow (e.arrow.symm b) := rfl
@[simp] lemma zigzagLinear_token (x : Q.Zigzag K) (v : W) :
    (e.zigzagLinear x).token v = x.token (e.vertex.symm v) := rfl

lemma zigzagLinear_one : e.zigzagLinear (1 : Q.Zigzag K) = 1 := rfl

lemma zigzagLinear_mul (x y : Q.Zigzag K) :
    e.zigzagLinear (x*y) = e.zigzagLinear x * e.zigzagLinear y := by
  apply Zigzag.ext
  · rfl
  · ext b
    simp only [zigzagLinear_arrow,Zigzag.arrow_mul,leftScale,rightScale,
      Pi.add_apply,zigzagLinear_vertex,e.source_symm,e.target_symm]
  · ext v
    simp only [zigzagLinear_token,Zigzag.token_mul,Pi.add_apply,Pi.mul_apply,
      zigzagLinear_vertex,backtrack]
    congr 1
    rw [← e.arrow.sum_comp]
    apply Finset.sum_congr rfl
    intro a _
    simp only [e.source,zigzagLinear_arrow,e.reverse,Equiv.symm_apply_apply]
    have hh : e.vertex (Q.source a)=v ↔ Q.source a=e.vertex.symm v :=
      e.vertex.eq_symm_apply.symm
    simp only [hh]

noncomputable def zigzag : Q.Zigzag K ≃+* R.Zigzag K where
  toEquiv := e.zigzagLinear.toEquiv
  map_mul' := e.zigzagLinear_mul
  map_add' := e.zigzagLinear.map_add

lemma zigzag_vertexId (v:V) : e.zigzagLinear (Zigzag.vertexId Q (K := K) v) =
    Zigzag.vertexId R (e.vertex v) := by
  apply Zigzag.ext
  · ext w
    simp only [zigzagLinear_vertex,Zigzag.vertexId_eval]
    congr 1
    exact propext e.vertex.symm_apply_eq
  · rfl
  · rfl

lemma zigzag_homogeneous {d : ℤ} {x : Q.Zigzag K} (h : Zigzag.Homogeneous Q d x) :
    Zigzag.Homogeneous R d (e.zigzagLinear x) := by
  refine ⟨?_,?_,?_⟩
  · intro hd; ext v; simp only [zigzagLinear_vertex,h.1 hd,Pi.zero_apply]
  · intro hd; ext b; simp only [zigzagLinear_arrow,h.2.1 hd,Pi.zero_apply]
  · intro hd; ext v; simp only [zigzagLinear_token,h.2.2 hd,Pi.zero_apply]

end Iso
end HarmonicArtin.ReversibleQuiver

end OAI
