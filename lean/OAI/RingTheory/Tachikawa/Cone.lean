import OAI.RingTheory.Tachikawa.DownHom

namespace OAI


noncomputable section
namespace Tachikawa
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
variable {R : Type} [Ring R]
namespace CompleteCone
variable {A B : ChainComplex (ModuleCat.{0} R) ℤ} (v : B ⟶ A)
abbrev complex := HomologicalComplex.homotopyCofiber v
private lemma rel (j : ℤ) : (ComplexShape.down ℤ).Rel j (j-1) := by
  change j-1+1=j; omega
abbrev left (j : ℤ) : (complex v).X j ⟶ B.X (j-1) :=
  HomologicalComplex.homotopyCofiber.fstX v j (j-1) (rel j)
abbrev right (j : ℤ) : (complex v).X j ⟶ A.X j :=
  HomologicalComplex.homotopyCofiber.sndX v j
abbrev inLeft (j : ℤ) : B.X (j-1) ⟶ (complex v).X j :=
  HomologicalComplex.homotopyCofiber.inlX v (j-1) j (rel j)
abbrev inRight (j : ℤ) : A.X j ⟶ (complex v).X j :=
  HomologicalComplex.homotopyCofiber.inrX v j

@[simp] lemma inLeft_left (j : ℤ) : inLeft v j ≫ left v j = 𝟙 _ := by
  apply HomologicalComplex.homotopyCofiber.inlX_fstX
@[simp] lemma inLeft_right (j : ℤ) : inLeft v j ≫ right v j = 0 := by
  apply HomologicalComplex.homotopyCofiber.inlX_sndX
@[simp] lemma inRight_left (j : ℤ) : inRight v j ≫ left v j = 0 := by
  apply HomologicalComplex.homotopyCofiber.inrX_fstX
@[simp] lemma inRight_right (j : ℤ) : inRight v j ≫ right v j = 𝟙 _ := by
  apply HomologicalComplex.homotopyCofiber.inrX_sndX
lemma total (j : ℤ) : left v j ≫ inLeft v j + right v j ≫ inRight v j = 𝟙 _ := by
  apply HomologicalComplex.homotopyCofiber.ext_to_X v j (j-1) (rel j) <;>
    simp only [add_comp,Category.assoc,inLeft_left,inLeft_right,inRight_left,
      inRight_right,Category.comp_id,comp_zero,zero_add,add_zero,Category.id_comp]

lemma ext_element (j : ℤ) {x y : (complex v).X j}
    (hl : left v j x = left v j y) (hr : right v j x = right v j y) : x = y := by
  have hx := congrArg (fun f => f x) (total v j)
  have hy := congrArg (fun f => f y) (total v j)
  change inLeft v j (left v j x) + inRight v j (right v j x) = x at hx
  change inLeft v j (left v j y) + inRight v j (right v j y) = y at hy
  rw [hl,hr,hy] at hx
  exact hx.symm

lemma left_d (j : ℤ) (x : (complex v).X j) :
    left v (j-1) ((complex v).d j (j-1) x) = - B.d (j-1) (j-1-1) (left v j x) := by
  exact congrArg (fun f => f x)
    (HomologicalComplex.homotopyCofiber.d_fstX v j (j-1) (j-1-1) (rel j) (rel (j-1)))
lemma right_d (j : ℤ) (x : (complex v).X j) :
    right v (j-1) ((complex v).d j (j-1) x) =
      v.f (j-1) (left v j x) + A.d j (j-1) (right v j x) := by
  exact congrArg (fun f => f x)
    (HomologicalComplex.homotopyCofiber.d_sndX v j (j-1) (rel j))
lemma inRight_d (i j : ℤ) : inRight v i ≫ (complex v).d i j = A.d i j ≫ inRight v j :=
  HomologicalComplex.homotopyCofiber.inrX_d v i j
lemma inLeft_d (j : ℤ) : inLeft v j ≫ (complex v).d j (j-1) =
    -B.d (j-1) (j-1-1) ≫ inLeft v (j-1) + v.f (j-1) ≫ inRight v (j-1) :=
  HomologicalComplex.homotopyCofiber.inlX_d v j (j-1) (j-1-1) (rel j) (rel (j-1))

lemma exact (hA : ComplexExact A) (hB : ComplexExact B) : ComplexExact (complex v) := by
  intro j x
  constructor
  · intro hx
    have hl : B.d (j-1) (j-1-1) (left v j x) = 0 := by
      have he := left_d v j x
      rw [hx,map_zero] at he
      exact neg_eq_zero.mp he.symm
    have hex := hB (j-1)
    rw [show j-1+1=j by omega] at hex
    obtain ⟨b,hb⟩ := (hex _).mp hl
    let y : (complex v).X (j+1) :=
      HomologicalComplex.homotopyCofiber.inlX v j (j+1) (by rfl) (-b)
    have hyl : left v j ((complex v).d (j+1) j y) = left v j x := by
      have he : HomologicalComplex.homotopyCofiber.inlX v j (j+1) (by rfl) ≫
          (complex v).d (j+1) j ≫ left v j = -B.d j (j-1) := by
        calc
          _ = (-B.d j (j-1) ≫ inLeft v j + v.f j ≫ inRight v j) ≫ left v j :=
            (Category.assoc _ _ _).symm.trans (congrArg (fun f => f ≫ left v j)
              (HomologicalComplex.homotopyCofiber.inlX_d v (j+1) j (j-1) (by rfl) (rel j)))
          _ = _ := by simp only [add_comp,neg_comp,Category.assoc,inLeft_left,inRight_left,
            Category.comp_id,comp_zero,add_zero]
      have he' := congrArg (fun f => f (-b)) he
      change left v j ((complex v).d (j+1) j y) = -(B.d j (j-1) (-b)) at he'
      rw [map_neg,neg_neg] at he'
      exact he'.trans hb
    let z := x - (complex v).d (j+1) j y
    have hzl : left v j z = 0 := by simp only [z,map_sub,hyl,sub_self]
    have hzd : (complex v).d j (j-1) z = 0 := by
      rw [map_sub,hx]
      have hd := congrArg (fun f => f y) ((complex v).d_comp_d (j+1) j (j-1))
      change (complex v).d j (j-1) ((complex v).d (j+1) j y) = 0 at hd
      rw [hd,sub_self]
    have hzr : A.d j (j-1) (right v j z) = 0 := by
      have he := right_d v j z
      rw [hzd,map_zero,hzl,map_zero,zero_add] at he
      exact he.symm
    obtain ⟨a,ha⟩ := (hA j _).mp hzr
    refine ⟨y + inRight v (j+1) a,?_⟩
    rw [map_add]
    have hd := congrArg (fun f => f a) (inRight_d v (j+1) j)
    change (complex v).d (j+1) j (inRight v (j+1) a) = inRight v j (A.d (j+1) j a) at hd
    rw [hd,ha]
    have hz : inRight v j (right v j z) = z := by
      apply ext_element v j
      · exact (congrArg (fun f => f (right v j z)) (inRight_left v j)).trans hzl.symm
      · exact congrArg (fun f => f (right v j z)) (inRight_right v j)
    rw [hz]
    dsimp only [z]
    rw [add_comm,sub_add_cancel]
  · rintro ⟨y,rfl⟩
    exact congrArg (fun f => f y) ((complex v).d_comp_d (j+1) j (j-1))

private lemma boundaries {P : ChainComplex (ModuleCat.{0} R) ℤ} (hP : TotallyAcyclic P)
    (j : ℤ) (f : P.X j ⟶ ModuleCat.of R R) (hf : P.d (j+1) j ≫ f = 0) :
    ∃ g : P.X (j-1) ⟶ ModuleCat.of R R, P.d j (j-1) ≫ g = f := by
  obtain ⟨g,hg⟩ := hP.2 j f.hom (ModuleCat.hom_ext_iff.mp hf)
  exact ⟨ModuleCat.ofHom g,ModuleCat.hom_ext hg⟩

lemma totallyAcyclic (hA : TotallyAcyclic A) (hB : TotallyAcyclic B) :
    TotallyAcyclic (complex v) := by
  refine ⟨exact v hA.1 hB.1,?_⟩
  intro j fl hfl
  let f : (complex v).X j ⟶ ModuleCat.of R R := ModuleCat.ofHom fl
  have hf : (complex v).d (j+1) j ≫ f = 0 := ModuleCat.hom_ext hfl
  have hfa : A.d (j+1) j ≫ (inRight v j ≫ f) = 0 := by
    rw [← Category.assoc,← inRight_d,Category.assoc,hf,comp_zero]
  obtain ⟨a,ha⟩ := boundaries hA j (inRight v j ≫ f) hfa
  let t := f - (complex v).d j (j-1) ≫ right v (j-1) ≫ a
  have htr : inRight v j ≫ t = 0 := by
    dsimp only [t]
    rw [comp_sub,← Category.assoc,← Category.assoc,inRight_d]
    simp only [Category.assoc]
    rw [← Category.assoc (inRight v (j-1)) (right v (j-1)) a,
      inRight_right,Category.id_comp,ha,sub_self]
  have htcy : (complex v).d (j+1) j ≫ t = 0 := by
    dsimp only [t]
    rw [comp_sub,hf,← Category.assoc,← Category.assoc,
      (complex v).d_comp_d,zero_comp,zero_comp,sub_self]
  let b := inLeft v j ≫ t
  have htb : t = left v j ≫ b := by
    calc
      t = (left v j ≫ inLeft v j + right v j ≫ inRight v j) ≫ t := by rw [total,Category.id_comp]
      _ = _ := by rw [add_comp,Category.assoc,Category.assoc,htr,comp_zero,add_zero]
  have hbcy : B.d j (j-1) ≫ b = 0 := by
    have he := congrArg (fun h => h ≫ t)
      (HomologicalComplex.homotopyCofiber.inlX_d v (j+1) j (j-1) (by rfl) (rel j))
    change (HomologicalComplex.homotopyCofiber.inlX v j (j+1) (by rfl) ≫
      (complex v).d (j+1) j) ≫ t =
      (-B.d j (j-1) ≫ inLeft v j + v.f j ≫ inRight v j) ≫ t at he
    simp only [Category.assoc,htcy,comp_zero,add_comp,neg_comp,htr,add_zero] at he
    exact neg_eq_zero.mp he.symm
  have hbound := boundaries hB (j-1)
  rw [show j-1+1=j by omega] at hbound
  obtain ⟨b',hb'⟩ := hbound b hbcy
  let g := right v (j-1) ≫ a - left v (j-1) ≫ b'
  have hg : (complex v).d j (j-1) ≫ g = f := by
    dsimp only [g]
    rw [comp_sub]
    have hd : (complex v).d j (j-1) ≫ left v (j-1) = -left v j ≫ B.d (j-1) (j-1-1) :=
      HomologicalComplex.homotopyCofiber.d_fstX v j (j-1) (j-1-1) (rel j) (rel (j-1))
    rw [← Category.assoc ( (complex v).d j (j-1)) (left v (j-1)) b',hd,
      neg_comp,Category.assoc,hb',← htb,sub_neg_eq_add]
    dsimp only [t]
    rw [add_comm,sub_add_cancel]
  exact ⟨g.hom,ModuleCat.hom_ext_iff.mp hg⟩

def termEquiv (j : ℤ) : (complex v).X j ≃ₗ[R] (B.X (j-1) × A.X j) :=
  (HomologicalComplex.homotopyCofiber.XIsoBiprod v j (j-1) (rel j) ≪≫
    ModuleCat.biprodIsoProd (B.X (j-1)) (A.X j)).toLinearEquiv

lemma finite (af : ∀ j, Module.Finite R (A.X j)) (bf : ∀ j, Module.Finite R (B.X j))
    (j : ℤ) : Module.Finite R ((complex v).X j) := by
  let := af j
  let := bf (j-1)
  exact Module.Finite.equiv (termEquiv v j).symm
lemma projective (ap : ∀ j, Module.Projective R (A.X j))
    (bp : ∀ j, Module.Projective R (B.X j)) (j : ℤ) :
    Module.Projective R ((complex v).X j) := by
  let := ap j
  let := bp (j-1)
  exact Module.Projective.of_equiv (termEquiv v j).symm

end CompleteCone
end Tachikawa



namespace Tachikawa.DownCone
open CategoryTheory CategoryTheory.Preadditive CategoryTheory.Limits HomologicalComplex
open scoped ModuleCat.Algebra
open DownHom CompleteCone
variable {k R : Type} [Field k] [CharP k 2] [Ring R] [Algebra k R]
variable {A B : ChainComplex (ModuleCat.{0} R) ℤ} (v : B ⟶ A)
abbrev C := complex v
abbrev iL (j : ℤ) := homotopyCofiber.inlX v j (j+1) (show (ComplexShape.down ℤ).Rel (j+1) j from rfl)
abbrev pL (j : ℤ) := homotopyCofiber.fstX v (j+1) j (show (ComplexShape.down ℤ).Rel (j+1) j from rfl)

def low {a : ℤ} (f : Cochain (C v) (C v) a) : Cochain A A a :=
  fun i j h => inRight v i ≫ f i j h ≫ right v j
def high {a : ℤ} (f : Cochain (C v) (C v) a) : Cochain B B a :=
  fun i j h => iL v i ≫ f (i+1) (j+1) (by omega) ≫ pL v j
def cross {a : ℤ} (f : Cochain (C v) (C v) a) : Cochain B A (a-1) :=
  fun i j h => iL v i ≫ f (i+1) j (by omega) ≫ right v j

def assemble {a : ℤ} (f : Cochain A A a) (g : Cochain B B a)
    (c : Cochain B A (a-1)) : Cochain (C v) (C v) a := fun i j h =>
  right v i ≫ f i j h ≫ inRight v j +
  left v i ≫ g (i-1) (j-1) (by omega) ≫ inLeft v j +
  left v i ≫ c (i-1) j (by omega) ≫ inRight v j

lemma inl_fst_apply {D : ChainComplex (ModuleCat.{0} R) ℤ} {a : ℤ}
    (f : Cochain B D a) (p p' t j : ℤ)
    (hp : (ComplexShape.down ℤ).Rel t p) (hp' : (ComplexShape.down ℤ).Rel t p')
    (he : p=j+a) (he' : p'=j+a) :
    homotopyCofiber.inlX v p t hp ≫ homotopyCofiber.fstX v t p' hp' ≫ f p' j he' = f p j he := by
  have hh : p'=p := by change p+1=t at hp; change p'+1=t at hp'; omega
  cases hh
  simp only [homotopyCofiber.inlX_fstX_assoc]
lemma apply_inl_fst {D : ChainComplex (ModuleCat.{0} R) ℤ} {a : ℤ}
    (f : Cochain D B a) (i p p' t : ℤ)
    (hp : (ComplexShape.down ℤ).Rel t p) (hp' : (ComplexShape.down ℤ).Rel t p')
    (he : i=p+a) (he' : i=p'+a) :
    f i p' he' ≫ homotopyCofiber.inlX v p' t hp' ≫ homotopyCofiber.fstX v t p hp = f i p he := by
  have hh : p'=p := by change p+1=t at hp; change p'+1=t at hp'; omega
  cases hh
  simp only [homotopyCofiber.inlX_fstX,Category.comp_id]
lemma block_transport {a : ℤ} (f : Cochain (C v) (C v) a)
    (p q i j i' j' : ℤ) (hi : (ComplexShape.down ℤ).Rel i p)
    (hi' : (ComplexShape.down ℤ).Rel i' p) (hj : (ComplexShape.down ℤ).Rel j q)
    (hj' : (ComplexShape.down ℤ).Rel j' q) (he : i=j+a) (he' : i'=j'+a) :
    homotopyCofiber.inlX v p i hi ≫ f i j he ≫ homotopyCofiber.fstX v j q hj =
    homotopyCofiber.inlX v p i' hi' ≫ f i' j' he' ≫ homotopyCofiber.fstX v j' q hj' := by
  have H : i'=i := by change p+1=i at hi; change p+1=i' at hi'; omega
  cases H
  have H : j'=j := by change q+1=j at hj; change q+1=j' at hj'; omega
  cases H; rfl
lemma cross_transport {a : ℤ} (f : Cochain (C v) (C v) a)
    (p i i' j : ℤ) (hi : (ComplexShape.down ℤ).Rel i p)
    (hi' : (ComplexShape.down ℤ).Rel i' p) (he : i=j+a) (he' : i'=j+a) :
    homotopyCofiber.inlX v p i hi ≫ f i j he ≫ right v j =
    homotopyCofiber.inlX v p i' hi' ≫ f i' j he' ≫ right v j := by
  have H : i'=i := by change p+1=i at hi; change p+1=i' at hi'; omega
  cases H; rfl

lemma low_assemble {a : ℤ} (f : Cochain A A a) (g : Cochain B B a) (c : Cochain B A (a-1)) :
    low v (assemble v f g c) = f := by
  funext i j h
  simp only [assemble,low,left,right,inLeft,inRight,comp_add,add_comp,
      Category.assoc,homotopyCofiber.inrX_fstX_assoc,
      homotopyCofiber.inrX_sndX_assoc,homotopyCofiber.inlX_sndX,
      homotopyCofiber.inrX_sndX,Category.comp_id,zero_comp,comp_zero,add_zero]
lemma high_assemble {a : ℤ} (f : Cochain A A a) (g : Cochain B B a) (c : Cochain B A (a-1)) :
    high v (assemble v f g c) = g := by
  funext i j h
  simp only [assemble,high,iL,pL,left,right,inLeft,inRight,add_comp,
      Category.assoc,homotopyCofiber.inrX_fstX,comp_zero,add_zero,zero_add]
  rw [apply_inl_fst v g _ j _ _ _ _ (by omega) _,inl_fst_apply v g _ _ _ _ _ _ h _]
lemma cross_assemble {a : ℤ} (f : Cochain A A a) (g : Cochain B B a) (c : Cochain B A (a-1)) :
    cross v (assemble v f g c) = c := by
  funext i j h
  simp only [assemble,cross,iL,left,right,inLeft,inRight,comp_add,add_comp,
      Category.assoc,homotopyCofiber.inlX_sndX_assoc,homotopyCofiber.inlX_sndX,
      homotopyCofiber.inrX_sndX,Category.comp_id,zero_comp,comp_zero,add_zero,zero_add]

  exact inl_fst_apply v c _ _ _ _ _ _ h _
variable (hAB : ∀ i j (f : A.X i ⟶ B.X j), f=0)
include hAB in
lemma assemble_blocks {a : ℤ} (f : Cochain (C v) (C v) a) :
    assemble v (low v f) (high v f) (cross v f) = f := by
  funext i j h
  apply homotopyCofiber.ext_from_X v (i-1) i (by change i-1+1=i; omega)
  · apply homotopyCofiber.ext_to_X v j (j-1) (by change j-1+1=j; omega)
    · simp only [assemble,low,high,cross,iL,pL,left,right,inLeft,inRight,comp_add,add_comp,
      Category.assoc,homotopyCofiber.inlX_fstX_assoc,homotopyCofiber.inlX_sndX_assoc,
      homotopyCofiber.inlX_fstX,homotopyCofiber.inrX_fstX,
      Category.comp_id,zero_comp,comp_zero,add_zero,zero_add]
      exact block_transport v f _ _ _ _ _ _ _ _ _ _ _ _

    · simp only [assemble,low,high,cross,iL,pL,left,right,inLeft,inRight,comp_add,add_comp,
      Category.assoc,homotopyCofiber.inlX_fstX_assoc,homotopyCofiber.inlX_sndX_assoc,
      homotopyCofiber.inlX_sndX,homotopyCofiber.inrX_sndX,
      Category.comp_id,zero_comp,comp_zero,zero_add]
      exact cross_transport v f _ _ _ _ _ _ _ _

  · apply homotopyCofiber.ext_to_X v j (j-1) (by change j-1+1=j; omega)
    · simpa only [assemble,low,high,cross,iL,pL,left,right,inLeft,inRight,comp_add,add_comp,
      Category.assoc,sub_add_cancel,add_sub_cancel_right,homotopyCofiber.inlX_fstX_assoc,
      homotopyCofiber.inlX_sndX_assoc,homotopyCofiber.inrX_fstX_assoc,
      homotopyCofiber.inrX_sndX_assoc,homotopyCofiber.inlX_fstX,
      homotopyCofiber.inlX_sndX,homotopyCofiber.inrX_fstX,
      homotopyCofiber.inrX_sndX,Category.id_comp,Category.comp_id,zero_comp,comp_zero,add_zero,zero_add] using (hAB i (j-1) (inRight v i ≫ f i j h ≫ left v j)).symm
    · simp only [assemble,low,high,cross,iL,pL,left,right,inLeft,inRight,comp_add,
      Category.assoc,homotopyCofiber.inrX_fstX_assoc,homotopyCofiber.inrX_sndX_assoc,
      homotopyCofiber.inrX_sndX,Category.comp_id,zero_comp,add_zero]

end Tachikawa.DownCone



namespace Tachikawa.DownCone
open CategoryTheory CategoryTheory.Preadditive CategoryTheory.Limits HomologicalComplex
open scoped ModuleCat.Algebra
open DownHom CompleteCone
variable {k R : Type} [Field k] [CharP k 2] [Ring R] [Algebra k R]
variable {A B : ChainComplex (ModuleCat.{0} R) ℤ} (v : B ⟶ A)

include k in
@[reassoc] lemma d_left (i : ℤ) : (C v).d i (i-1) ≫ left v (i-1) =
    left v i ≫ B.d (i-1) (i-1-1) := by
  have h := homotopyCofiber.d_fstX v i (i-1) (i-1-1)
    (by change i-1+1=i; omega) (by change i-1-1+1=i-1; omega)
  change (C v).d i (i-1) ≫ left v (i-1) = -(left v i) ≫ B.d (i-1) (i-1-1) at h
  rw [negative (k := k)] at h
  exact h
@[reassoc] lemma d_right (i : ℤ) : (C v).d i (i-1) ≫ right v (i-1) =
    left v i ≫ v.f (i-1) + right v i ≫ A.d i (i-1) :=
  homotopyCofiber.d_sndX v i (i-1) (by change i-1+1=i; omega)
@[reassoc] lemma inRight_dcat (i j : ℤ) : inRight v i ≫ (C v).d i j =
    A.d i j ≫ inRight v j := inRight_d v i j
include k in
lemma apply_inl_d {D : ChainComplex (ModuleCat.{0} R) ℤ} {a : ℤ}
    (f : Cochain D B a) (i s t j : ℤ)
    (hs : (ComplexShape.down ℤ).Rel t s) (hj : (ComplexShape.down ℤ).Rel t j)
    (he : i=s+a) (he' : i=j+a) :
    f i s he ≫ homotopyCofiber.inlX v s t hs ≫ (C v).d t j =
    f i j he' ≫ B.d j (j-1) ≫ inLeft v j + f i j he' ≫ v.f j ≫ inRight v j := by
  have H : s=j := by change s+1=t at hs; change j+1=t at hj; omega
  cases H
  change f i s he ≫ homotopyCofiber.inlX v s t hs ≫ homotopyCofiber.d v t s = _
  rw [homotopyCofiber.inlX_d v t s (s-1) hs (by change s-1+1=s; omega)]
  rw [comp_add,negative (k := k)]

include k in
lemma diff_assemble {a : ℤ} (f : Cochain A A (a-1)) (g : Cochain B B (a-1))
    (c : Cochain B A (a-1-1)) :
    diff (assemble v f g c) =
      assemble v (diff f) (diff g) (diff c + pre v f + post g v) := by
  funext i j h
  simp only [diff,assemble,DownHom.add_apply,pre,post,comp_add,add_comp,Category.assoc,
    d_left_assoc (k := k),d_right_assoc,inRight_dcat]
  rw [apply_inl_d (k := k) v g (i-1) (j+1-1) (j+1) j
    (by change j+1-1+1=j+1; omega) (by rfl) _ (by omega)]
  simp only [comp_add]
  rw [← Category.assoc (g (i-1) (j-1+1) _) (B.d (j-1+1) (j-1)) (inLeft v j),
    d_post_eq g (i-1) (j-1+1) j (j-1) (by omega) _ (by omega),Category.assoc]
  abel

variable (hAB : ∀ i j (f : A.X i ⟶ B.X j), f=0)
include hAB k

lemma low_diff {a : ℤ} (f : Cochain (C v) (C v) (a-1)) :
    low v (diff f) = diff (low v f) := by
  conv_lhs => rw [← assemble_blocks v hAB f,diff_assemble (k := k),low_assemble]
lemma high_diff {a : ℤ} (f : Cochain (C v) (C v) (a-1)) :
    high v (diff f) = diff (high v f) := by
  conv_lhs => rw [← assemble_blocks v hAB f,diff_assemble (k := k),high_assemble]
lemma cross_diff {a : ℤ} (f : Cochain (C v) (C v) (a-1)) :
    cross v (diff f) = diff (cross v f) + pre v (low v f) + post (high v f) v := by
  conv_lhs => rw [← assemble_blocks v hAB f,diff_assemble (k := k),cross_assemble]

end Tachikawa.DownCone



namespace Tachikawa.DownCone
open CategoryTheory CategoryTheory.Preadditive CategoryTheory.Limits
open scoped ModuleCat.Algebra
open DownHom CompleteCone
variable {k R : Type} [Field k] [CharP k 2] [Ring R] [Algebra k R]
variable {A B : ChainComplex (ModuleCat.{0} R) ℤ} (v : B ⟶ A)

@[simp] lemma low_zero (a : ℤ) : low v (0 : Cochain (C v) (C v) a) = 0 := by
  funext i j h; simp [low]
@[simp] lemma high_zero (a : ℤ) : high v (0 : Cochain (C v) (C v) a) = 0 := by
  funext i j h; simp [high]
@[simp] lemma cross_zero (a : ℤ) : cross v (0 : Cochain (C v) (C v) a) = 0 := by
  funext i j h; simp [cross]
@[simp] lemma low_add {a : ℤ} (f g : Cochain (C v) (C v) a) :
    low v (f+g) = low v f+low v g := by funext i j h; simp [low,comp_add,add_comp]
@[simp] lemma high_add {a : ℤ} (f g : Cochain (C v) (C v) a) :
    high v (f+g) = high v f+high v g := by funext i j h; simp [high,comp_add,add_comp]
@[simp] lemma cross_add {a : ℤ} (f g : Cochain (C v) (C v) a) :
    cross v (f+g) = cross v f+cross v g := by funext i j h; simp [cross,comp_add,add_comp]

variable (hAB : ∀ i j (f : A.X i ⟶ B.X j), f=0)
include hAB in
lemma blocks_ext {a : ℤ} {f g : Cochain (C v) (C v) a}
    (hl : low v f = low v g) (hh : high v f = high v g) (hc : cross v f = cross v g) : f=g := by
  rw [← assemble_blocks v hAB f,← assemble_blocks v hAB g,hl,hh,hc]

include hAB k in
lemma closed_blocks_aux {a : ℤ} : ∀ (f : Cochain (C v) (C v) (a-1)), Closed f →
    Closed (low v f) ∧ Closed (high v f) ∧
      pre v (low v f)+post (high v f) v = diff (cross v f) := by
  intro f hf
  have hz := (closed_iff_diff_zero (k := k) f).mp hf
  refine ⟨(closed_iff_diff_zero (k := k) _).mpr ?_,
    (closed_iff_diff_zero (k := k) _).mpr ?_,?_⟩
  · rw [← low_diff (k := k) v hAB,hz,low_zero]
  · rw [← high_diff (k := k) v hAB,hz,high_zero]
  · have hh := congrArg (cross v) hz
    rw [cross_diff (k := k) v hAB,cross_zero,add_assoc] at hh
    exact (eq_neg_of_add_eq_zero_right hh).trans (negative (k := k) _)

include hAB k in
lemma closed_blocks {a : ℤ} (f : Cochain (C v) (C v) a) (hf : Closed f) :
    Closed (low v f) ∧ Closed (high v f) ∧
      pre v (low v f)+post (high v f) v = diff (cross v f) := by
  have hh := closed_blocks_aux (k := k) v hAB (a := a+1)
  rw [show a+1-1=a by omega] at hh
  exact hh f hf

include k hAB in

theorem boundary_of_delta (a : ℤ)
    (hI : ∀ (f : Cochain A A a) (g : Cochain B B a),
      Closed f → Closed g → Boundary (pre v f+post g v) → Boundary f ∧ Boundary g)
    (hS : ∀ (c : Cochain B A (a-1)), Closed c →
      ∃ (f : Cochain A A (a-1)) (g : Cochain B B (a-1)),
        Closed f ∧ Closed g ∧ Boundary (c+pre v f+post g v))
    (z : Cochain (C v) (C v) a) (hz : Closed z) : Boundary z := by
  obtain ⟨hf,hg,he⟩ := closed_blocks (k := k) v hAB z hz
  have hb : Boundary (pre v (low v z)+post (high v z) v) := he ▸ boundary_diff (cross v z)
  obtain ⟨hbf,hbg⟩ := hI _ _ hf hg hb
  obtain ⟨s,hs⟩ := (boundary_iff_diff _).mp hbf
  obtain ⟨t,ht⟩ := (boundary_iff_diff _).mp hbg
  let b := diff (assemble v s t 0)
  let zz := z+b
  have hzz : Closed zz := closed_add hz (diff_closed _)
  have hl : low v zz = 0 := by
    dsimp only [zz,b]
    rw [low_add,low_diff (k := k) v hAB,low_assemble,hs]
    exact twice (k := k) _
  have hh : high v zz = 0 := by
    dsimp only [zz,b]
    rw [high_add,high_diff (k := k) v hAB,high_assemble,ht]
    exact twice (k := k) _
  have hc : Closed (cross v zz) := by
    apply (closed_iff_diff_zero (k := k) _).mpr
    have he := (closed_blocks (k := k) v hAB zz hzz).2.2
    rw [hl,hh] at he
    have h0 : pre v (0 : Cochain A A a)+post (0 : Cochain B B a) v = 0 := by
      funext i j he; simp [pre,post]
    exact he.symm.trans h0
  obtain ⟨f,g,hf,hg,hc⟩ := hS (cross v zz) hc
  obtain ⟨c,hc⟩ := (boundary_iff_diff _).mp hc
  have hf0 : diff f = (0 : Cochain A A a) := (closed_iff_diff_zero (k := k) f).mp hf
  have hg0 : diff g = (0 : Cochain B B a) := (closed_iff_diff_zero (k := k) g).mp hg
  have hd : diff (assemble v f g c) = zz := by
    apply blocks_ext v hAB
    · rw [low_diff (k := k) v hAB,low_assemble,hf0,hl]
    · rw [high_diff (k := k) v hAB,high_assemble,hg0,hh]
    · rw [cross_diff (k := k) v hAB,cross_assemble,low_assemble,high_assemble,← hc]
      have htw := twice (k := k) (pre v f+post g v)
      calc
        _ = cross v zz + ((pre v f+post g v)+(pre v f+post g v)) := by abel
        _ = _ := by rw [htw,add_zero]
  have hzB : Boundary zz := hd ▸ boundary_diff (assemble v f g c)
  have hbB : Boundary b := boundary_diff _
  have hsum : zz+b=z := by
    dsimp only [zz]
    rw [add_assoc,twice (k := k) b,add_zero]
  exact hsum ▸ boundary_add hzB hbB
end Tachikawa.DownCone



namespace Tachikawa.Triangular
open CategoryTheory
open DownHom
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [CharP k 2] [Ring R] [Algebra k R]
variable (F : ModuleCat.{0} (Enveloping.Alg k R R))
  {P : ChainComplex (ModuleCat.{0} R) ℤ}
  (u : P ⟶ Enveloping.tensorComplex F P)
abbrev cone := CompleteCone.complex (crossMap F u)

include k in
lemma cone_closed_boundary (a : ℤ)
    (hI : ∀ (f g : Cochain P P a), Closed f → Closed g →
      Boundary (actionDelta (Enveloping.tensorFunctor F) u f g) → Boundary f ∧ Boundary g)
    (hS : ∀ (c : Cochain P (Enveloping.tensorComplex F P) (a-1)), Closed c →
      ∃ (f g : Cochain P P (a-1)), Closed f ∧ Closed g ∧
        Boundary (c+actionDelta (Enveloping.tensorFunctor F) u f g))
    (z : Cochain (cone F u) (cone F u) a) (hz : Closed z) : Boundary z := by
  apply DownCone.boundary_of_delta (k := k) (crossMap F u) (fun _ _ f => cross₀₁_zero f) a ?_ ?_ z hz
  · intro f g hf hg hb
    have hh := (downCross_boundary F _).mpr hb
    rw [downCross_delta] at hh
    obtain ⟨h0,h1⟩ := hI (down₀ F a f) (down₁ F a g)
      ((down₀_closed F f).mpr hf) ((down₁_closed F g).mpr hg) hh
    exact ⟨(down₀_boundary F f).mp h0,(down₁_boundary F g).mp h1⟩
  · intro c hc
    obtain ⟨f,g,hf,hg,hb⟩ := hS (downCross F (a-1) c) ((downCross_closed F c).mpr hc)
    let f' := (down₀ F (a-1)).symm f
    let g' := (down₁ F (a-1)).symm g
    have h0 : down₀ F (a-1) f'=f := LinearEquiv.apply_symm_apply _ _
    have h1 : down₁ F (a-1) g'=g := LinearEquiv.apply_symm_apply _ _
    refine ⟨f',g',(down₀_closed F f').mp (h0.symm ▸ hf),
      (down₁_closed F g').mp (h1.symm ▸ hg),?_⟩
    apply (downCross_boundary F _).mp
    rw [add_assoc,map_add,downCross_delta,h0,h1]
    exact hb
end Tachikawa.Triangular



namespace Tachikawa.Triangular
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable (F : ModuleCat.{0} (Enveloping.Alg k R R))
abbrev oneFree := freeObj (R := R) (PUnit : Type)
instance : Module.Finite R (oneFree (R := R)) := inferInstanceAs (Module.Finite R (PUnit → R))
instance : Module.Projective R (oneFree (R := R)) := inferInstanceAs (Module.Projective R (PUnit → R))
def regIn₀ : D₀Obj F (oneFree (R := R)) →ₗ[Alg F] Alg F :=
  (LinearMap.proj PUnit.unit).comp (D₀FreeInclusion F PUnit)
def regIn₁ : D₁Obj F (oneFree (R := R)) →ₗ[Alg F] Alg F :=
  (LinearMap.proj PUnit.unit).comp (D₁FreeInclusion F PUnit)
def regOut₀ : Alg F →ₗ[Alg F] D₀Obj F (oneFree (R := R)) :=
  (D₀FreeProjection F PUnit).comp (LinearMap.pi fun _ => LinearMap.id)
def regOut₁ : Alg F →ₗ[Alg F] D₁Obj F (oneFree (R := R)) :=
  (D₁FreeProjection F PUnit).comp (LinearMap.pi fun _ => LinearMap.id)
lemma reg_split : (regIn₀ F).comp (regOut₀ F) + (regIn₁ F).comp (regOut₁ F) = LinearMap.id := by
  apply LinearMap.ext
  intro a
  apply TrivSqZeroExt.ext
  · apply Prod.ext
    · change upper F a + 0 = a.fst.1
      exact add_zero _
    · change 0 + lower F a = a.fst.2
      exact zero_add _
  · change freeTensorEval F PUnit (freeTensorInv F PUnit (fun _ => off F a)) PUnit.unit + 0 = a.snd
    rw [freeTensorEval_inv,add_zero]
    rfl

variable (P : ChainComplex (ModuleCat.{0} R) ℤ) (hP : TotallyAcyclic P)
  [Module.Finite Rᵐᵒᵖ (Enveloping.Obj F)] [Module.Projective Rᵐᵒᵖ (Enveloping.Obj F)]
include hP in
lemma D₀_totallyAcyclic : TotallyAcyclic (D₀Complex F P) := by
  refine ⟨fun j => D₀Map_exact F _ _ (hP.1 j),?_⟩
  intro j f hf
  let f₀ : D₀Obj F (P.X j) ⟶ D₀Obj F (oneFree (R := R)) := ModuleCat.ofHom ((regOut₀ F).comp f)
  have hf₀ : D₀Map F (P.d (j+1) j) ≫ f₀ = 0 := by
    apply ModuleCat.hom_ext
    change ((regOut₀ F).comp f).comp ((D₀Complex F P).d (j+1) j).hom = 0
    rw [LinearMap.comp_assoc,hf,LinearMap.comp_zero]
  obtain ⟨g₀,hg₀⟩ := D₀_boundaries F P hP (oneFree (R := R)) j f₀ hf₀
  have hf₁ : (regOut₁ F).comp f = 0 :=
    ModuleCat.hom_ext_iff.mp (cross₀₁_zero (ModuleCat.ofHom ((regOut₁ F).comp f)))
  refine ⟨(regIn₀ F).comp g₀.hom,?_⟩
  have hg := ModuleCat.hom_ext_iff.mp hg₀
  change g₀.hom.comp ((D₀Complex F P).d j (j-1)).hom = (regOut₀ F).comp f at hg
  erw [LinearMap.comp_assoc,hg]
  have hs := congrArg (fun p : Alg F →ₗ[Alg F] Alg F => p.comp f) (reg_split F)
  rw [LinearMap.add_comp,LinearMap.comp_assoc,LinearMap.comp_assoc,hf₁,
    LinearMap.comp_zero,add_zero,LinearMap.id_comp] at hs
  exact hs

variable [FiniteDimensional k (Enveloping.Obj F)] [Module.Projective R (Enveloping.Obj F)]
include hP in
omit [Module.Finite Rᵐᵒᵖ (Enveloping.Obj F)] [Module.Projective Rᵐᵒᵖ (Enveloping.Obj F)] in
lemma D₁_totallyAcyclic : TotallyAcyclic (D₁Complex F P) := by
  let N := oneFree (R := R)
  let : Module.Finite R N := inferInstanceAs (Module.Finite R (PUnit → R))
  let : Module.Projective R N := inferInstanceAs (Module.Projective R (PUnit → R))
  let : Module.Finite R (tensorObj F N) := by
    let : Module.Finite R (Enveloping.Obj F) := Module.Finite.of_restrictScalars_finite k _ _
    exact Module.Finite.equiv (freeTensorEquiv F PUnit).symm
  let : Module.Projective R (tensorObj F N) :=
    BalancedTensor.map_projective (k := k) (R := R) (S := R) (M := Enveloping.Obj F) (N := N)
  refine ⟨fun j => D₁Map_exact F _ _ (hP.1 j),?_⟩
  intro j f hf
  let f₀ : D₁Obj F (P.X j) ⟶ D₀Obj F N := ModuleCat.ofHom ((regOut₀ F).comp f)
  let f₁ : D₁Obj F (P.X j) ⟶ D₁Obj F N := ModuleCat.ofHom ((regOut₁ F).comp f)
  have hf₀ : D₁Map F (P.d (j+1) j) ≫ f₀ = 0 := by
    apply ModuleCat.hom_ext
    change ((regOut₀ F).comp f).comp ((D₁Complex F P).d (j+1) j).hom = 0
    rw [LinearMap.comp_assoc,hf,LinearMap.comp_zero]
  have hf₁ : D₁Map F (P.d (j+1) j) ≫ f₁ = 0 := by
    apply ModuleCat.hom_ext
    change ((regOut₁ F).comp f).comp ((D₁Complex F P).d (j+1) j).hom = 0
    rw [LinearMap.comp_assoc,hf,LinearMap.comp_zero]
  obtain ⟨g₀,hg₀⟩ := cross_boundaries F P hP N j f₀ hf₀
  obtain ⟨g₁,hg₁⟩ := D₁_boundaries F P hP N j f₁ hf₁
  refine ⟨(regIn₀ F).comp g₀.hom + (regIn₁ F).comp g₁.hom,?_⟩
  have hg₀ := ModuleCat.hom_ext_iff.mp hg₀
  have hg₁ := ModuleCat.hom_ext_iff.mp hg₁
  change g₀.hom.comp ((D₁Complex F P).d j (j-1)).hom = (regOut₀ F).comp f at hg₀
  change g₁.hom.comp ((D₁Complex F P).d j (j-1)).hom = (regOut₁ F).comp f at hg₁
  change (regIn₀ F).comp (g₀.hom.comp ((D₁Complex F P).d j (j-1)).hom) +
    (regIn₁ F).comp (g₁.hom.comp ((D₁Complex F P).d j (j-1)).hom) = f
  rw [hg₀,hg₁]
  exact congrArg (fun p : Alg F →ₗ[Alg F] Alg F => p.comp f) (reg_split F)

end Tachikawa.Triangular



namespace Tachikawa.DownHom
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable (P : ChainComplex (ModuleCat.{0} R) ℤ) (hP : TotallyAcyclic P)
  (pP : ∀ j, Module.Projective R (P.X j)) (fP : ∀ j, Module.Finite R (P.X j))
include hP pP fP in
lemma homology_subsingleton (a : ℤ)
    (hb : ∀ (f : Cochain P P a), Closed f → Boundary f) :
    Subsingleton (VectorSplit.H (completeHom (k := k) P (ModuleCat.of R (CokerAt P 0))) a) := by
  let ε : P.X 0 ⟶ ModuleCat.of R (CokerAt P 0) := ModuleCat.ofHom (CokerAt.π P 0)
  have hε : P.d 1 0 ≫ ε = 0 := by
    apply ModuleCat.hom_ext
    exact CokerAt.π_d P 0
  have he : Function.Exact (P.d 1 0) ε := fun x => Submodule.Quotient.mk_eq_zero _
  have hs : Function.Surjective ε := CokerAt.π_surjective P 0
  have hz : ∀ x : VectorSplit.H (completeHom (k := k) P (ModuleCat.of R (CokerAt P 0))) a, x=0 := by
    intro x
    obtain ⟨f,hf,hx⟩ := eval_surjective ε hε hP hP.1 pP fP pP he hs a x
    rw [← hx]
    exact eval_boundary ε hε f hf (hb f hf)
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩
end Tachikawa.DownHom



namespace Tachikawa.Triangular
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable (F : ModuleCat.{0} (Enveloping.Alg k R R))
  [FiniteDimensional k R] [FiniteDimensional k F]
  [Module.Projective R (Enveloping.Obj F)] [Module.Projective Rᵐᵒᵖ (Enveloping.Obj F)]
  {P : ChainComplex (ModuleCat.{0} R) ℤ} (u : P ⟶ Enveloping.tensorComplex F P)
  (hP : TotallyAcyclic P) (fP : ∀ j, Module.Finite R (P.X j))
  (pP : ∀ j, Module.Projective R (P.X j))
include hP in
omit [FiniteDimensional k R] in
lemma cone_totallyAcyclic : TotallyAcyclic (cone F u) := by
  let : FiniteDimensional k (Enveloping.Obj F) := inferInstanceAs (FiniteDimensional k F)
  let : Module.Finite Rᵐᵒᵖ (Enveloping.Obj F) := Module.Finite.of_restrictScalars_finite k _ _
  exact CompleteCone.totallyAcyclic _ (D₀_totallyAcyclic F P hP) (D₁_totallyAcyclic F P hP)
include fP in
omit [Module.Projective R (Enveloping.Obj F)] [Module.Projective Rᵐᵒᵖ (Enveloping.Obj F)] in
lemma cone_finite (j : ℤ) : Module.Finite (Alg F) ((cone F u).X j) := by
  apply CompleteCone.finite
  · intro i
    let := fP i
    let : FiniteDimensional k (P.X i) := Module.Finite.trans R _
    change Module.Finite (Alg F) (D₀Obj F (P.X i))
    exact Module.Finite.of_restrictScalars_finite k _ _
  · intro i
    let := fP i
    let : FiniteDimensional k (P.X i) := Module.Finite.trans R _
    change Module.Finite (Alg F) (D₁Obj F (P.X i))
    exact Module.Finite.of_restrictScalars_finite k _ _
include fP pP in
omit [FiniteDimensional k R] [FiniteDimensional k F]
  [Module.Projective R (Enveloping.Obj F)] [Module.Projective Rᵐᵒᵖ (Enveloping.Obj F)] in
lemma cone_projective (j : ℤ) : Module.Projective (Alg F) ((cone F u).X j) := by
  apply CompleteCone.projective
  · intro i
    let := fP i
    let := pP i
    exact D₀_projective F (P.X i)
  · intro i
    let := fP i
    let := pP i
    exact D₁_projective F (P.X i)
end Tachikawa.Triangular



namespace Tachikawa.DownHom
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [CharP k 2] [Ring R] [Algebra k R]
variable (P : ChainComplex (ModuleCat.{0} R) ℤ) (X : ModuleCat.{0} R)
  (ε : P.X 0 ⟶ X) (hε : P.d 1 0 ≫ ε = 0)
  (hP : TotallyAcyclic P) (pP : ∀ j, Module.Projective R (P.X j))
  (fP : ∀ j, Module.Finite R (P.X j))
  (heP : Function.Exact (P.d 1 0) ε) (hsP : Function.Surjective ε)
  (F : ModuleCat.{0} R ⥤ ModuleCat.{0} R) [F.Additive] [F.Linear k]
  (u : P ⟶ mapComplex F P) (u₀ : X ⟶ F.obj X)
  (hu : u.f 0 ≫ F.map ε = ε ≫ u₀)
include hε hP pP fP heP hsP hu in
omit [CharP k 2] in
lemma actionDelta_injective (a : ℤ) (hI : Function.Injective (homologyDelta (k := k) F X u u₀ a))
    (f g : Cochain P P a) (hf : Closed f) (hg : Closed g)
    (hb : Boundary (actionDelta F u f g)) : Boundary f ∧ Boundary g := by
  have hz := eval_boundary (k := k) (F.map ε) (map_augmentation_zero F X ε hε)
    (actionDelta F u f g) (actionDelta_closed F u hf hg) hb
  rw [eval_actionDelta F X ε hε u u₀ hu f g hf hg] at hz
  have he : (evalClass (k := k) ε hε f hf,evalClass (k := k) ε hε g hg) = 0 :=
    hI (hz.trans (map_zero _).symm)
  constructor
  · exact boundary_of_eval_zero ε hε hP hP.1 pP fP fP pP heP hsP f hf
      (congrArg Prod.fst he)
  · exact boundary_of_eval_zero ε hε hP hP.1 pP fP fP pP heP hsP g hg
      (congrArg Prod.snd he)

variable (hQ : ComplexExact (mapComplex F P))
  (fQ : ∀ j, Module.Finite R ((mapComplex F P).X j))
  (pQ : ∀ j, Module.Projective R ((mapComplex F P).X j))
  (heQ : Function.Exact ((mapComplex F P).d 1 0) (F.map ε))
  (hsQ : Function.Surjective (F.map ε))
include hε hP pP fP heP hsP hQ fQ pQ heQ hsQ hu in
lemma actionDelta_surjective (a : ℤ)
    (hS : Function.Surjective (homologyDelta (k := k) F X u u₀ a))
    (c : Cochain P (mapComplex F P) a) (hc : Closed c) :
    ∃ (f g : Cochain P P a), Closed f ∧ Closed g ∧ Boundary (c+actionDelta F u f g) := by
  let hεQ := map_augmentation_zero F X ε hε
  obtain ⟨⟨x,y⟩,hxy⟩ := hS (evalClass (k := k) (F.map ε) hεQ c hc)
  obtain ⟨f,hf,heF⟩ := eval_surjective ε hε hP hP.1 pP fP pP heP hsP a x
  obtain ⟨g,hg,heG⟩ := eval_surjective ε hε hP hP.1 pP fP pP heP hsP a y
  refine ⟨f,g,hf,hg,?_⟩
  apply boundary_of_eval_zero (k := k) (F.map ε) hεQ hP hQ pP fP fQ pQ heQ hsQ
    (c+actionDelta F u f g) (closed_add hc (actionDelta_closed F u hf hg))
  rw [eval_add _ _ _ _ hc (actionDelta_closed F u hf hg),
    eval_actionDelta F X ε hε u u₀ hu f g hf hg,heF,heG,hxy]
  exact twice (k := k) _
end Tachikawa.DownHom

end

end OAI
