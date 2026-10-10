import OAI.RingTheory.DirectFiniteness.SlabAssembly

namespace OAI

universe u_1 u_2 u_3 u_4

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q : Type u_1} {A : Type u_2} {R : Type u_3} {E : Type u_4} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E] [Fintype A] [Fintype Q]
namespace DirectionFrame
variable (F : DirectionFrame Q A R E)

lemma coset_range_eq_line (f : Q →ₗ[Q] A) (o : A) :
    cosetPoints f.range o = linePoints (Q := Q) o (f 1) := by
  ext y
  rw [mem_cosetPoints,mem_linePoints]
  constructor
  · rintro ⟨t,ht⟩
    exact ⟨t,by rw [← f.map_smul]; simpa using (eq_add_of_sub_eq' ht.symm).symm⟩
  · rintro ⟨t,rfl⟩
    exact ⟨t,by simp [← map_smul]⟩

lemma coset_range_full (f : Q →ₗ[Q] A) (hf : Function.Injective f) (o : A) :
    FullLine (Q := Q) (cosetPoints f.range o) := by
  rw [coset_range_eq_line]
  exact ⟨o,f 1,fun h => one_ne_zero (hf (h.trans f.map_zero.symm)),rfl⟩

def replacementLine (r : R) (o : A) (a : Q) : Finset A :=
  cosetPoints (F.exceptional r) (o+F.w r (a,0))

omit [Fintype Q] in
lemma mem_replacementLine (r : R) (o x : A) (a : Q) :
    x ∈ F.replacementLine r o a ↔ ∃ b : Q, F.w r (a,b)=x-o := by
  rw [replacementLine, mem_cosetPoints]
  change (∃ b : Q, F.exc r b = x - (o + F.w r (a, 0))) ↔ _
  constructor
  · rintro ⟨b,hb⟩
    refine ⟨b,?_⟩
    have he : (a,b)=(a,0)+(0,b) := by simp
    rw [he,map_add,← F.exc_apply,hb]
    abel
  · rintro ⟨b,hb⟩
    refine ⟨b,?_⟩
    have he : (0,b)=(a,b)-(a,0) := by simp
    rw [exc_apply,he,map_sub,hb]
    abel

lemma replacementLine_full (r : R) (o : A) (a : Q) :
    FullLine (Q := Q) (F.replacementLine r o a) := coset_range_full (F.exc r) (F.exc_injective r) _

omit [Fintype Q] in
lemma replacementLine_subset (r : R) (o : A) (a : Q) :
    F.replacementLine r o a ⊆ cosetPoints (F.W r) o := by
  intro x hx
  obtain ⟨b,hb⟩ := (F.mem_replacementLine r o x a).mp hx
  exact (mem_cosetPoints _ _ _).mpr ⟨(a,b),hb⟩

omit [Fintype Q] in
lemma replacementLine_hole_free (S O : Finset A)
    (hO : HoleEvents.GoodHoles S F.W F.U (fun r t => F.exc r t) O)
    (r : R) (o : O) (a : Q) (ha : a ≠ 0) : Disjoint (F.replacementLine r o.val a) O := by
  rw [Finset.disjoint_left]
  intro x hx hxO
  have hxo := hO.collision r o.val o.property x hxO ((mem_cosetPoints _ _ _).mp (F.replacementLine_subset r o.val a hx))
  obtain ⟨b,hb⟩ := (F.mem_replacementLine r o.val x a).mp hx
  rw [hxo,sub_self] at hb
  have he := F.winj r (hb.trans (F.w r).map_zero.symm)
  exact ha (congrArg Prod.fst he)

omit [Fintype Q] in
lemma replacementLine_same_label (S O : Finset A)
    (hO : HoleEvents.GoodHoles S F.W F.U (fun r t => F.exc r t) O)
    {r : R} {o o' : O} {a a' : Q} {x : A}
    (hx : x ∈ F.replacementLine r o.val a) (hx' : x ∈ F.replacementLine r o'.val a') :
    o=o' ∧ a=a' := by
  obtain ⟨b,hb⟩ := (F.mem_replacementLine r o.val x a).mp hx
  obtain ⟨b',hb'⟩ := (F.mem_replacementLine r o'.val x a').mp hx'
  have hdiff : o'.val-o.val ∈ F.W r := by
    convert (F.W r).sub_mem (show x-o.val ∈ F.W r from ⟨(a,b),hb⟩)
      (show x-o'.val ∈ F.W r from ⟨(a',b'),hb'⟩) using 1; abel
  have hoo' : o'=o := Subtype.ext (hO.collision r o.val o.property o'.val o'.property hdiff)
  subst o'
  exact ⟨rfl,congrArg Prod.fst (F.winj r (hb.trans hb'.symm))⟩

omit [Fintype Q] in
lemma replacementLine_step {r : R} {o x y : A} {a : Q}
    (hx : x ∈ F.replacementLine r o a) (hy : y ∈ F.replacementLine r o a)
    (hne : y ≠ x) : ∃ t : Q, t ≠ 0 ∧ F.exc r t=y-x := by
  obtain ⟨b,hb⟩ := (F.mem_replacementLine r o x a).mp hx
  obtain ⟨c,hc⟩ := (F.mem_replacementLine r o y a).mp hy
  have he : F.exc r (c-b)=y-x := by
    change F.w r (0,c-b)=_
    have he' : (0,c-b)=(a,c)-(a,b) := by simp
    rw [he',map_sub,hc,hb]
    abel
  refine ⟨c-b,?_,he⟩
  intro hz
  rw [hz,map_zero] at he
  exact hne (sub_eq_zero.mp he.symm)

end DirectionFrame
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
