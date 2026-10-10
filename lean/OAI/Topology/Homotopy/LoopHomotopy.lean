import Mathlib

namespace OAI

/-! Loop-space homeomorphisms and the degree-shift equivalence. -/

noncomputable section
universe u v w


namespace NearbyLagrangian.BasedHomotopy
open ContinuousMap
open scoped Topology Topology.Homotopy
variable {N M X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable {x : X} {y : Y}

theorem genLoop_homotopic_iff_joined (f g : GenLoop N X x) :
    GenLoop.Homotopic f g ↔ Joined f g := by
  constructor
  · rintro ⟨H⟩
    refine ⟨{
      toFun := fun s => ⟨H.toContinuousMap.curry s,fun t ht =>
        (H.prop s t ht).trans (GenLoop.boundary f t ht)⟩
      continuous_toFun := H.toContinuousMap.curry.continuous.subtype_mk _
      source' := ?_
      target' := ?_ }⟩
    · ext t; exact H.apply_zero t
    · ext t; exact H.apply_one t
  · rintro ⟨P⟩
    refine ⟨{
      toFun := fun z => P z.1 z.2
      continuous_toFun := ?_
      map_zero_left := ?_
      map_one_left := ?_
      prop' := ?_ }⟩
    · exact (continuous_subtype_val.comp (P.continuous.comp continuous_fst)).eval continuous_snd
    · intro t; exact congrArg (fun z : GenLoop N X x => z t) P.source
    · intro t; exact congrArg (fun z : GenLoop N X x => z t) P.target
    · intro s t ht
      exact (GenLoop.boundary (P s) t ht).trans (GenLoop.boundary f t ht).symm

def piEquivOfLoopHomeomorph (e : GenLoop N X x ≃ₜ GenLoop M Y y) :
    HomotopyGroup N X x ≃ HomotopyGroup M Y y :=
  Quotient.congr e.toEquiv fun f g => by
    change GenLoop.Homotopic f g ↔ GenLoop.Homotopic (e f) (e g)
    rw [genLoop_homotopic_iff_joined,genLoop_homotopic_iff_joined]
    constructor
    · intro h; exact h.map e.continuous_toFun
    · intro h
      have hh : Joined (e.symm (e f)) (e.symm (e g)) := h.map e.symm.continuous_toFun
      simpa only [Homeomorph.symm_apply_apply] using hh

def piReindexEquiv (e : N ≃ M) (x : X) :
    HomotopyGroup N X x ≃ HomotopyGroup M X x :=
  piEquivOfLoopHomeomorph (GenLoop.congr x e)

def flattenPathLoop (f : GenLoop N (Path y y) (Path.refl y)) :
    GenLoop (N ⊕ Unit) Y y :=
  ⟨⟨fun a => f (a ∘ Sum.inl) (a (Sum.inr ())),by
    apply Continuous.eval
    · exact f.1.continuous.comp (by fun_prop)
    · fun_prop⟩,by
      rintro a ⟨i | i,hi⟩ <;> change f (a ∘ Sum.inl) (a (Sum.inr ())) = y
      · have h : a ∘ Sum.inl ∈ Cube.boundary N := ⟨i,hi⟩
        rw [GenLoop.boundary f _ h]
        rfl
      · cases i
        rcases hi with hi | hi
        · rw [hi]; exact (f _).source
        · rw [hi]; exact (f _).target⟩

def curryPathLoop (g : GenLoop (N ⊕ Unit) Y y) :
    GenLoop N (Path y y) (Path.refl y) :=
  ⟨⟨fun a => {
    toFun := fun r => g (Sum.elim a (fun _ => r))
    continuous_toFun := g.1.continuous.comp (by apply continuous_pi; intro i; cases i <;> dsimp only [Sum.elim] <;> fun_prop)
    source' := GenLoop.boundary g _ ⟨Sum.inr (),Or.inl rfl⟩
    target' := GenLoop.boundary g _ ⟨Sum.inr (),Or.inr rfl⟩ },by
      apply Path.continuous_uncurry_iff.mp
      exact g.1.continuous.comp (by apply continuous_pi; intro i; cases i <;> dsimp only [Sum.elim] <;> fun_prop)⟩,by
    rintro a ⟨i,hi⟩
    apply Path.ext
    funext r
    exact GenLoop.boundary g _ ⟨Sum.inl i,hi⟩⟩

@[simp] lemma curry_flatten (f : GenLoop N (Path y y) (Path.refl y)) :
    curryPathLoop (flattenPathLoop f) = f := by
  apply Subtype.ext
  ext a r
  rfl

@[simp] lemma flatten_curry (g : GenLoop (N ⊕ Unit) Y y) :
    flattenPathLoop (curryPathLoop g) = g := by
  apply Subtype.ext
  ext a
  change g (Sum.elim (a ∘ Sum.inl) (fun _ => a (Sum.inr ()))) = g a
  congr 1
  funext i
  cases i with
  | inl i => rfl
  | inr i => cases i; rfl

lemma continuous_flattenPathLoop : Continuous (@flattenPathLoop N Y _ y) := by
  apply Continuous.subtype_mk
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun z : GenLoop N (Path y y) (Path.refl y) × ((N ⊕ Unit) → unitInterval) =>
    z.1 (z.2 ∘ Sum.inl) (z.2 (Sum.inr ())))
  have h : Continuous (fun z : GenLoop N (Path y y) (Path.refl y) × ((N ⊕ Unit) → unitInterval) =>
      z.1 (z.2 ∘ Sum.inl)) :=
    (continuous_subtype_val.comp continuous_fst).eval
      (continuous_pi (fun i => (continuous_apply (Sum.inl i)).comp continuous_snd))
  exact h.eval ((continuous_apply (Sum.inr ())).comp continuous_snd)

lemma continuous_curryPathLoop : Continuous (@curryPathLoop N Y _ y) := by
  apply Continuous.subtype_mk
  apply ContinuousMap.continuous_of_continuous_uncurry
  apply Path.continuous_uncurry_iff.mp
  exact (continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).eval
    (by apply continuous_pi; intro i; cases i <;> dsimp only [Sum.elim] <;> fun_prop)

def loopSpaceCubeHomeomorph :
    GenLoop N (Path y y) (Path.refl y) ≃ₜ GenLoop (N ⊕ Unit) Y y where
  toFun := flattenPathLoop
  invFun := curryPathLoop
  left_inv := curry_flatten
  right_inv := flatten_curry
  continuous_toFun := continuous_flattenPathLoop
  continuous_invFun := continuous_curryPathLoop

def loopPiEquiv (y : Y) :
    HomotopyGroup N (Path y y) (Path.refl y) ≃ HomotopyGroup (N ⊕ Unit) Y y :=
  piEquivOfLoopHomeomorph loopSpaceCubeHomeomorph

def pi9LoopEquivPi10 (y : Y) :
    π_ 9 (Path y y) (Path.refl y) ≃ π_ 10 Y y :=
  (loopPiEquiv y).trans (piReindexEquiv
    ((Equiv.sumCongr (Equiv.refl (Fin 9)) (Equiv.ofUnique Unit (Fin 1))).trans finSumFinEquiv) y)

end NearbyLagrangian.BasedHomotopy

end

end OAI
