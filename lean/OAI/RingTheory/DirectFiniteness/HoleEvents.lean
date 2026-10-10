import OAI.RingTheory.DirectFiniteness.Alteration

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.FiniteGeometry

lemma card_sup_le_mul {Q : Type u_1} {A : Type u_2} [Field Q] [AddCommGroup A] [Module Q A]
    [Fintype A] (U W : Submodule Q A) :
    Fintype.card ↥(U ⊔ W) ≤ Fintype.card U * Fintype.card W := by
  let f : U × W → ↥(U ⊔ W) := fun x => ⟨x.1.val + x.2.val,
    (U ⊔ W).add_mem ((show U ≤ U ⊔ W from le_sup_left) x.1.property) ((show W ≤ U ⊔ W from le_sup_right) x.2.property)⟩
  have hf : Function.Surjective f := by
    rintro ⟨x,hx⟩
    obtain ⟨u,hu,w,hw,he⟩ := Submodule.mem_sup.mp hx
    exact ⟨(⟨u,hu⟩,⟨w,hw⟩),Subtype.ext he⟩
  simpa only [Fintype.card_prod] using Fintype.card_le_of_surjective f hf

lemma card_bounded_tuples {α : Type u_3} [Fintype α] [DecidableEq α] (n B : ℕ) (p : Fin n → α → Prop)
    (hp : ∀ i, Fintype.card {x // p i x} ≤ B) :
    Fintype.card {f : Fin n → α // Function.Injective f ∧ ∀ i, p i (f i)} ≤ B^n := by
  let f : {f : Fin n → α // Function.Injective f ∧ ∀ i, p i (f i)} →
      (i : Fin n) → {x // p i x} := fun x i => ⟨x.val i,x.property.2 i⟩
  have hf : Function.Injective f := by
    intro u v h
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun h i)
  apply (Fintype.card_le_of_injective f hf).trans
  rw [Fintype.card_pi]
  calc
    (∏ i : Fin n, Fintype.card {x // p i x}) ≤ ∏ _ : Fin n, B :=
      Finset.prod_le_prod (fun i _ => hp i)
    _ = B^n := by simp

namespace HoleEvents
variable {Q : Type u_4} {A : Type u_5} {R : Type u_6} [Field Q] [AddCommGroup A] [Module Q A]
  [Fintype Q] [Fintype A] [Fintype R]
variable (S : Finset A) (W : R → Submodule Q A) (U : R × Q → Submodule Q A)

def PairIndex := Σ r : R, Σ x : S, {y : S // y ≠ x ∧ y.val - x.val ∈ W r}
instance : Fintype (PairIndex S W) := by unfold PairIndex; infer_instance

def pairSet (i : PairIndex S W) : Finset S := {i.2.1,i.2.2.val}

omit [Fintype Q] [Fintype A] [Fintype R] in
lemma pairSet_card (i : PairIndex S W) : (pairSet S W i).card = 2 := by
  simp [pairSet,Ne.symm i.2.2.property.1]

omit [Fintype Q] [Fintype R] in
lemma card_source_fiber (r : R) (x : A) :
    Fintype.card {y : S // y.val - x ∈ W r} ≤ Fintype.card (W r) := by
  let f : {y : S // y.val - x ∈ W r} → W r := fun y => ⟨y.val.val-x,y.property⟩
  apply Fintype.card_le_of_injective f
  intro y z h
  apply Subtype.ext
  apply Subtype.ext
  have he := congrArg (fun t : W r => (t : A) + x) h
  simpa only [f,sub_add_cancel] using he

omit [Fintype Q] in
lemma pairIndex_card (d : ℕ) (hW : ∀ r, Fintype.card (W r) ≤ d) :
    Fintype.card (PairIndex S W) ≤ Fintype.card R * S.card * d := by
  simp only [PairIndex,Fintype.card_sigma]
  calc
    (∑ r : R, ∑ x : S,
      Fintype.card {y : S // y ≠ x ∧ y.val - x.val ∈ W r})
      ≤ ∑ _r : R, ∑ _x : S, d := by
        apply Finset.sum_le_sum; intro r _
        apply Finset.sum_le_sum; intro x _
        exact (Fintype.card_subtype_mono _ _ (fun _ h => h.2)).trans
          ((card_source_fiber S W r x.val).trans (hW r))
    _ = Fintype.card R * S.card * d := by simp [mul_assoc]

def OccupancyIndex (k : ℕ) := Σ j : R × Q, Σ r : R, Σ x : A,
  {f : Fin k → S // Function.Injective f ∧ ∀ i, (f i).val-x ∈ U j ⊔ W r}
instance (k : ℕ) : Fintype (OccupancyIndex S W U k) := by
  unfold OccupancyIndex; infer_instance

def occupancySet {k : ℕ} (i : OccupancyIndex S W U k) : Finset S :=
  Finset.univ.image i.2.2.2.val

omit [Fintype Q] [Fintype A] [Fintype R] in
lemma occupancySet_card {k : ℕ} (i : OccupancyIndex S W U k) :
    (occupancySet S W U i).card = k := by
  rw [occupancySet,Finset.card_image_of_injective _ i.2.2.2.property.1]
  simp

lemma occupancyIndex_card (k d : ℕ) (hU : ∀ j r, Fintype.card ↥(U j ⊔ W r) ≤ d) :
    Fintype.card (OccupancyIndex S W U k) ≤
      (Fintype.card R * Fintype.card Q) * Fintype.card R * Fintype.card A * d^k := by
  simp only [OccupancyIndex,Fintype.card_sigma]
  calc
    _ ≤ ∑ _j : R × Q, ∑ _r : R, ∑ _x : A, d^k := by
      apply Finset.sum_le_sum; intro j _
      apply Finset.sum_le_sum; intro r _
      apply Finset.sum_le_sum; intro x _
      apply card_bounded_tuples k d (fun _ (y : S) => y.val - x ∈ U j ⊔ W r)
      intro i
      exact (card_source_fiber S (fun _ : Unit => U j ⊔ W r) () x).trans (hU j r)
    _ = _ := by simp [mul_assoc]

/-- Four cyclic corners, with side labels r,r',r,r'. -/
def corner (e : R → Q → A) (r r' : R) (x : A) (u v : Q) : Fin 4 → A :=
  ![x,x+e r u,x+e r u+e r' v,x+e r' v]

def sideLabel (r r' : R) : Fin 4 → R := ![r,r',r,r']

def RectangleIndex (e : R → Q → A) := Σ r : R, Σ r' : R, Σ x : A, Σ u : Q, Σ v : Q,
  {f : Fin 4 → S // Function.Injective f ∧ ∀ i,
      (f i).val - corner e r r' x u v i ∈ W (sideLabel r r' i)}
instance (e : R → Q → A) : Fintype (RectangleIndex S W e) := by
  unfold RectangleIndex; infer_instance

def rectangleSet {e : R → Q → A} (i : RectangleIndex S W e) : Finset S :=
  Finset.univ.image i.2.2.2.2.2.val

omit [Fintype Q] [Fintype A] [Fintype R] in
lemma rectangleSet_card {e : R → Q → A} (i : RectangleIndex S W e) :
    (rectangleSet S W i).card = 4 := by
  rw [rectangleSet,Finset.card_image_of_injective _ i.2.2.2.2.2.property.1]
  simp

lemma rectangleIndex_card (e : R → Q → A) (d : ℕ) (hW : ∀ r, Fintype.card (W r) ≤ d) :
    Fintype.card (RectangleIndex S W e) ≤
      (Fintype.card R)^2 * Fintype.card A * (Fintype.card Q)^2 * d^4 := by
  simp only [RectangleIndex,Fintype.card_sigma]
  calc
    _ ≤ ∑ _r : R, ∑ _r' : R, ∑ _x : A, ∑ _u : Q, ∑ _v : Q, d^4 := by
      apply Finset.sum_le_sum; intro r _
      apply Finset.sum_le_sum; intro r' _
      apply Finset.sum_le_sum; intro x _
      apply Finset.sum_le_sum; intro u _
      apply Finset.sum_le_sum; intro v _
      apply card_bounded_tuples 4 d (fun i (y : S) => y.val - corner e r r' x u v i ∈ W (sideLabel r r' i))
      intro i
      exact (card_source_fiber S W (sideLabel r r' i) (corner e r r' x u v i)).trans
        (hW (sideLabel r r' i))
    _ = _ := by simp; ring

end HoleEvents
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
