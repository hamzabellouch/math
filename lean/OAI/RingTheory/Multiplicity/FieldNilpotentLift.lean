import Mathlib

namespace OAI

noncomputable section
open Polynomial IntermediateField
namespace Lech.FieldLift
universe u v
variable {k : Type u} {A : Type v} [Field k] [CommRing A]
  (p : ℕ) [Fact p.Prime] [CharP k p] [CharP A p]
  (J : Ideal A) (hJ : J^p=⊥) (f : k →+* A ⧸ J)
include hJ

lemma pow_eq_of_quotient_eq {x y : A} (h : Ideal.Quotient.mk J x=Ideal.Quotient.mk J y) :
    x^p=y^p := by
  have hh := Ideal.pow_mem_pow (Ideal.Quotient.eq.mp h) p
  rw [hJ,Ideal.mem_bot] at hh
  rw [sub_pow_char] at hh
  exact sub_eq_zero.mp hh

omit hJ in
def liftElement (a : k) : A := (Ideal.Quotient.mk_surjective (f a)).choose
omit hJ in
lemma liftElement_spec (a : k) : Ideal.Quotient.mk J (liftElement J f a)=f a :=
  (Ideal.Quotient.mk_surjective (f a)).choose_spec

 
def powLift : k →+* A where
  toFun a := (liftElement J f a)^p
  map_one' := by
    calc
      (liftElement J f 1)^p=(1:A)^p := pow_eq_of_quotient_eq p J hJ (by rw [liftElement_spec,map_one,map_one])
      _=1 := one_pow p
  map_mul' a b := by
    rw [← mul_pow]
    apply pow_eq_of_quotient_eq p J hJ
    simp only [map_mul,liftElement_spec]
  map_zero' := by
    calc
      (liftElement J f 0)^p=(0:A)^p := pow_eq_of_quotient_eq p J hJ (by rw [liftElement_spec,map_zero,map_zero])
      _=0 := zero_pow (Fact.out : p.Prime).ne_zero
  map_add' a b := by
    rw [← add_pow_char]
    apply pow_eq_of_quotient_eq p J hJ
    simp only [map_add,liftElement_spec]

omit [CharP k p] in
lemma powLift_eq {a : k} {x : A} (hx : Ideal.Quotient.mk J x=f a) :
    powLift p J hJ f a = x^p :=
  pow_eq_of_quotient_eq p J hJ ((liftElement_spec J f a).trans hx.symm)

omit [CharP k p] in
lemma powLift_mod (a : k) : Ideal.Quotient.mk J (powLift p J hJ f a)=f (a^p) := by
  change Ideal.Quotient.mk J ((liftElement J f a)^p)=_
  rw [map_pow,liftElement_spec,map_pow]

end Lech.FieldLift

namespace Lech.FieldPartialLift
variable (F E A : Type*) [Field F] [Field E] [CommRing A] [Algebra F E] [Algebra F A]
 
structure Lifts where
  carrier : IntermediateField F E
  emb : carrier →ₐ[F] A
variable {F E A}
namespace Lifts
instance : PartialOrder (Lifts F E A) where
  le L₁ L₂ := ∃ h : L₁.carrier ≤ L₂.carrier, ∀ x, L₂.emb (inclusion h x)=L₁.emb x
  le_refl L := ⟨le_rfl,by simp⟩
  le_trans L₁ L₂ L₃ := by
    rintro ⟨h₁₂,h₁₂'⟩ ⟨h₂₃,h₂₃'⟩
    refine ⟨h₁₂.trans h₂₃,fun x => ?_⟩
    rw [← inclusion_inclusion h₁₂ h₂₃,h₂₃',h₁₂']
  le_antisymm := by
    rintro ⟨L₁,e₁⟩ ⟨L₂,e₂⟩ ⟨h₁₂,h₁₂'⟩ ⟨h₂₁,h₂₁'⟩
    obtain rfl : L₁=L₂ := h₁₂.antisymm h₂₁
    congr
    exact AlgHom.ext h₂₁'
noncomputable instance : OrderBot (Lifts F E A) where
  bot := ⟨⊥,(Algebra.ofId F A).comp (botEquiv F E)⟩
  bot_le L := ⟨bot_le,fun x => by
    obtain ⟨x,rfl⟩ := (botEquiv F E).symm.surjective x
    simp_rw [AlgHom.comp_apply,AlgEquiv.coe_toAlgHom,AlgEquiv.apply_symm_apply]
    exact L.emb.commutes x⟩

variable (c : Set (Lifts F E A)) (hc : IsChain (· ≤ ·) c)
noncomputable def union : Lifts F E A :=
  let t (i : ↑(insert ⊥ c)) := i.val.carrier
  have hc := hc.insert fun _ _ _ => .inl bot_le
  have dir : Directed (· ≤ ·) t := hc.directedOn.directed_val.mono_comp _ fun _ _ h => h.1
  ⟨iSup t, (Subalgebra.iSupLift (toSubalgebra <| t ·) dir (·.val.emb) (fun i j h =>
    AlgHom.ext fun x => (hc.total i.2 j.2).elim (fun hij => (hij.snd x).symm) fun hji => by
      rw [AlgHom.comp_apply, ← inclusion]
      dsimp only [coe_type_toSubalgebra]
      rw [← hji.snd (inclusion h x), inclusion_inclusion, inclusion_self, AlgHom.id_apply x])
    _ le_rfl).comp
      (Subalgebra.equivOfEq _ _ <| toSubalgebra_iSup_of_directed dir)⟩

lemma le_union {σ : Lifts F E A} (hσ : σ ∈ c) : σ ≤ union c hc := by
  let t (i : ↑(insert ⊥ c)) := i.val.carrier
  refine ⟨le_iSup t ⟨σ,Or.inr hσ⟩,fun x => ?_⟩
  dsimp only [union,AlgHom.comp_apply]
  have hc' := hc.insert fun _ _ _ => .inl bot_le
  have dir : Directed (· ≤ ·) t := hc'.directedOn.directed_val.mono_comp _ fun _ _ h => h.1
  have compatible (i j : ↑(insert ⊥ c)) (h : (t i).toSubalgebra ≤ (t j).toSubalgebra) :
      i.val.emb = j.val.emb.comp (Subalgebra.inclusion h) := by
    apply AlgHom.ext
    intro x
    exact (hc'.total i.2 j.2).elim (fun hij => (hij.snd x).symm) (fun hji => by
      rw [AlgHom.comp_apply, ← inclusion]
      rw [← hji.snd (inclusion h x), inclusion_inclusion, inclusion_self, AlgHom.id_apply x])
  exact Subalgebra.iSupLift_inclusion (K := (toSubalgebra <| t ·)) (f := fun i => i.val.emb)
    (dir := dir) (hf := compatible) (hT := le_rfl)
    (i:=⟨σ,Or.inr hσ⟩) x (le_iSup (toSubalgebra <| t ·) ⟨σ,Or.inr hσ⟩)
end Lifts
end Lech.FieldPartialLift

namespace Lech.FieldPartialLift
open Lifts
variable {F E A Q : Type*} [Field F] [Field E] [CommRing A] [CommRing Q]
  [Algebra F E] [Algebra F A] [Algebra F Q]
  (p : ℕ) [Fact p.Prime] [CharP E p]
  (f : E →ₐ[F] Q) (t : A →ₐ[F] Q)
lemma extend_root (φ : Lifts F E A)
    (hφ : ∀ y : φ.carrier,t (φ.emb y)=f y)
    (a : E) (ha : a ∉ φ.carrier) (c : F) (hc : algebraMap F E c=a^p)
    (x : A) (hx : t x=f a) (hxp : x^p=algebraMap F A c) :
    ∃ ψ : Lifts F E A,φ < ψ ∧ ∀ y : ψ.carrier,t (ψ.emb y)=f y := by
  let L := φ.carrier
  let : Algebra L A := φ.emb.toAlgebra
  let : Algebra L Q := (f.comp L.val).toAlgebra
  let g : L[X] := X^p-C (algebraMap F L c)
  have hirr : Irreducible g := by
    apply (X_pow_sub_C_irreducible_iff_of_prime (Fact.out : p.Prime)).mpr
    intro b hb
    apply ha
    have hbE := congrArg (algebraMap L E) hb
    have he : (b:E)^p=a^p := by
      change (b:E)^p=algebraMap F E c at hbE
      exact hbE.trans hc
    have hb' : (b:E)=a := (frobenius E p).injective he
    exact hb' ▸ b.2
  have hzero : aeval a g=0 := by
    simp only [g,map_sub,map_pow,aeval_X,aeval_C]
    change a^p-algebraMap F E c=0
    rw [hc,sub_self]
  have hm : g.Monic := monic_X_pow_sub_C (algebraMap F L c) (Fact.out : p.Prime).ne_zero
  have haI : IsIntegral L a := ⟨g,hm,hzero⟩
  have hmin : minpoly L a=g := (minpoly.eq_of_irreducible_of_monic hirr hzero hm).symm
  let pb := IntermediateField.adjoin.powerBasis haI
  have hxpoly : aeval x (minpoly L pb.gen)=0 := by
    rw [IntermediateField.adjoin.powerBasis_gen,IntermediateField.minpoly_gen,hmin]
    simp only [g,map_sub,map_pow,aeval_X,aeval_C]
    change x^p-φ.emb (algebraMap F L c)=0
    rw [φ.emb.commutes c,hxp,sub_self]
  let b := pb.lift x hxpoly
  let ψ : Lifts F E A := ⟨L⟮a⟯.restrictScalars F,b.restrictScalars F⟩
  refine ⟨ψ,?_,?_⟩
  · apply lt_iff_le_not_ge.mpr
    have hL : φ ≤ ψ := ⟨by
      change L ≤ L⟮a⟯.restrictScalars F
      rw [IntermediateField.restrictScalars_adjoin_eq_sup]
      exact le_sup_left,fun y => b.commutes y⟩
    refine ⟨hL,?_⟩
    intro hh
    exact ha (hh.1 (IntermediateField.subset_adjoin L {a} (Set.mem_singleton a)))
  · let tL : A →ₐ[L] Q := {t.toRingHom with commutes' := hφ}
    let fL : E →ₐ[L] Q := {f.toRingHom with commutes' := fun _ => rfl}
    have he : tL.comp b=fL.comp L⟮a⟯.val := by
      apply pb.algHom_ext
      rw [AlgHom.comp_apply,PowerBasis.lift_gen]
      exact hx
    intro y
    exact AlgHom.congr_fun he y
end Lech.FieldPartialLift

namespace Lech.FieldPartialLift
open Lifts
variable {F E A Q : Type*} [Field F] [Field E] [CommRing A] [CommRing Q]
  [Algebra F E] [Algebra F A] [Algebra F Q]
  (p : ℕ) [Fact p.Prime] [CharP E p]
  (f : E →ₐ[F] Q) (t : A →ₐ[F] Q)
lemma bot_compatible : ∀ y : (⊥ : Lifts F E A).carrier,t ((⊥ : Lifts F E A).emb y)=f y := by
  intro y
  obtain ⟨a,rfl⟩ := (IntermediateField.botEquiv F E).symm.surjective y
  change t (((Algebra.ofId F A).comp (botEquiv F E)) ((botEquiv F E).symm a))=_
  simp only [AlgHom.comp_apply,AlgEquiv.coe_toAlgHom,AlgEquiv.apply_symm_apply]
  rw [show ((botEquiv F E).symm a : E)=algebraMap F E a from rfl]
  exact (t.commutes a).trans (f.commutes a).symm

lemma mem_union (c : Set (Lifts F E A)) (hc : IsChain (· ≤ ·) c)
    (y : E) (hy : y ∈ (Lifts.union c hc).carrier) :
    ∃ φ ∈ insert ⊥ c,y ∈ φ.carrier := by
  let T (i : ↑(insert ⊥ c)) := i.val.carrier
  have hc' := hc.insert (fun _ _ _ => Or.inl (bot_le : (⊥ : Lifts F E A) ≤ _))
  have hd : Directed (· ≤ ·) T := hc'.directedOn.directed_val.mono_comp _ fun _ _ h => h.1
  change y ∈ ⨆ i,T i at hy
  rw [← SetLike.mem_coe,IntermediateField.coe_iSup_of_directed hd,Set.mem_iUnion] at hy
  obtain ⟨i,hi⟩ := hy
  exact ⟨i.val,i.2,hi⟩

lemma compatible_of_mem {φ ψ : Lifts F E A} (h : φ ≤ ψ)
    (hφ : ∀ z : φ.carrier,t (φ.emb z)=f z) (y : ψ.carrier) (hy : (y:E) ∈ φ.carrier) :
    t (ψ.emb y)=f y := by
  let z : φ.carrier := ⟨y,hy⟩
  have hz : inclusion h.1 z=y := rfl
  rw [← hz,h.2]
  exact hφ z

lemma union_compatible (c : Set (Lifts F E A)) (hc : IsChain (· ≤ ·) c)
    (H : ∀ φ ∈ c, ∀ y : φ.carrier,t (φ.emb y)=f y) :
    ∀ y : (Lifts.union c hc).carrier,t ((Lifts.union c hc).emb y)=f y := by
  intro y
  obtain ⟨φ,hφ,hy⟩ := mem_union c hc y y.2
  have hle : φ ≤ Lifts.union c hc := by
    rcases hφ with rfl | he
    · exact bot_le
    · exact Lifts.le_union c hc he
  have hiC : ∀ z : φ.carrier,t (φ.emb z)=f z := by
    rcases hφ with rfl | he
    · exact bot_compatible f t
    · exact H _ he
  exact compatible_of_mem f t hle hiC y hy

lemma exists_lift_of_roots
    (H : ∀ a : E,∃ c : F,algebraMap F E c=a^p ∧
      ∃ x : A,t x=f a ∧ x^p=algebraMap F A c) :
    ∃ g : E →ₐ[F] A,t.comp g=f := by
  obtain ⟨φ,hφ⟩ := zorn_le₀ {φ : Lifts F E A | ∀ y : φ.carrier,t (φ.emb y)=f y}
    (fun c hC hc => ⟨Lifts.union c hc,union_compatible f t c hc hC,
      fun σ hσ => Lifts.le_union c hc hσ⟩)
  have hcompat := hφ.1
  have htop : φ.carrier=⊤ := by
    by_contra hn
    obtain ⟨a,_,ha⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hn)
    obtain ⟨c,hc,x,hx,hxp⟩ := H a
    obtain ⟨ψ,hlt,hψ⟩ := extend_root p f t φ hcompat a ha c hc x hx hxp
    exact (not_lt_of_ge (hφ.2 hψ hlt.le)) hlt
  let e : φ.carrier ≃ₐ[F] E := (IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv
  refine ⟨φ.emb.comp e.symm.toAlgHom,?_⟩
  ext a
  exact hcompat (e.symm a)
end Lech.FieldPartialLift

namespace Lech.FieldLift
variable {k A : Type*} [Field k] [CommRing A]
  (p : ℕ) [Fact p.Prime] [CharP k p] [CharP A p]
  (J : Ideal A) (hJ : J^p=⊥) (f : k →+* A ⧸ J)
include p hJ
 

theorem exists_lift : ∃ g : k →+* A,(Ideal.Quotient.mk J).comp g=f := by
  let F := (frobenius k p).fieldRange
  let e : k ≃+* F := (frobenius k p).rangeRestrictFieldEquiv
  let τ : F →+* A := (powLift p J hJ f).comp e.symm.toRingHom
  let : Algebra F A := τ.toAlgebra
  let : Algebra F (A ⧸ J) := (f.comp (frobenius k p).fieldRange.subtype).toAlgebra
  let t : A →ₐ[F] A ⧸ J := {Ideal.Quotient.mk J with
    commutes' := fun c => by
      change Ideal.Quotient.mk J (powLift p J hJ f (e.symm c))=f (c:k)
      rw [powLift_mod]
      exact congrArg f ((frobenius k p).rangeRestrictFieldEquiv_apply_symm_apply c) }
  let f' : k →ₐ[F] A ⧸ J := {f with commutes' := fun _ => rfl}
  obtain ⟨g,hg⟩ := FieldPartialLift.exists_lift_of_roots p f' t (fun a => by
    refine ⟨e a,rfl,liftElement J f a,liftElement_spec J f a,?_⟩
    change (liftElement J f a)^p=powLift p J hJ f (e.symm (e a))
    rw [e.symm_apply_apply]
    rfl)
  exact ⟨g.toRingHom,congrArg AlgHom.toRingHom hg⟩
end Lech.FieldLift

namespace Lech.FieldLift
variable {k A Q : Type*} [Field k] [CommRing A] [CommRing Q]
  (p : ℕ) [Fact p.Prime] [CharP k p] [CharP A p]
 
theorem exists_lift_surjective (t : A →+* Q) (ht : Function.Surjective t)
    (hker : (RingHom.ker t)^p=⊥) (f : k →+* Q) :
    ∃ g : k →+* A,t.comp g=f := by
  let e := RingHom.quotientKerEquivOfSurjective ht
  obtain ⟨g,hg⟩ := exists_lift p (RingHom.ker t) hker (e.symm.toRingHom.comp f)
  refine ⟨g,?_⟩
  apply RingHom.ext
  intro x
  have hh := RingHom.congr_fun hg x
  have hh' := congrArg e hh
  simpa [e] using hh'
end Lech.FieldLift

end

end OAI
