import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.CosetVertex
import OAI.Topology.ArtinGroups.Harmonic.ReducedExpression
import OAI.Topology.ArtinGroups.Coxeter.InverseParabolicMinimum

namespace OAI

namespace HarmonicArtin
universe v
variable {S : Type v}

lemma coxeterParabolic_mono (M : CoxeterMatrix S) {J K : Set S} (h : J ⊆ K) :
    coxeterParabolic M J ≤ coxeterParabolic M K := Subgroup.closure_mono (Set.image_mono h)

lemma wordCoxeter_append (M : CoxeterMatrix S) (u v : List S) :
    wordCoxeter M (u++v)=wordCoxeter M u*wordCoxeter M v := by
  simp only [wordCoxeter,List.map_append,List.prod_append]

lemma wordCoxeter_mem_parabolic (M : CoxeterMatrix S) (J : Set S) (u : List S)
    (hu : ∀ i ∈ u, i ∈ J) : wordCoxeter M u ∈ coxeterParabolic M J :=
  CoxeterExchange.wordProd_mem_parabolic M.toCoxeterSystem J u hu

lemma liftedFace_refl (M : CoxeterMatrix S) (a : LiftedCell M) : LiftedFace M a a := by
  refine ⟨Set.Subset.rfl, [], by simp, ?_, ?_, ?_⟩
  · simp [wordCoxeter]
  · intro v
    simp only [wordCoxeter,List.map_nil,List.prod_nil,M.toCoxeterSystem.length_one]
    exact Nat.zero_le _
  · simp [wordArtin]

lemma liftedFace_trans (M : CoxeterMatrix S) {a b c : LiftedCell M}
    (hab : LiftedFace M a b) (hbc : LiftedFace M b c) : LiftedFace M a c := by
  obtain ⟨hAB,u,hu,hur,humin,ha⟩ := hab
  obtain ⟨hBC,v,hv,hvr,hvmin,hb⟩ := hbc
  have huB := wordCoxeter_mem_parabolic M b.2.1 u hu
  have hvadd : ∀ w ∈ coxeterParabolic M b.2.1,
      M.toCoxeterSystem.length (wordCoxeter M v*w) =
        M.toCoxeterSystem.length (wordCoxeter M v)+M.toCoxeterSystem.length w := by
    intro w hw
    exact CoxeterExchange.length_mul_of_right_minimum M.toCoxeterSystem b.2.1
      (wordCoxeter M v) (fun x hx => hvmin ⟨x,hx⟩) w hw
  refine ⟨hAB.trans hBC,v++u,?_,?_,?_,?_⟩
  · intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · exact hv i hi
    · exact hBC (hu i hi)
  · rw [wordCoxeter_append,hvadd _ huB,hvr,hur,List.length_append]
  · intro w
    have hwB : (w : M.Group) ∈ coxeterParabolic M b.2.1 := coxeterParabolic_mono M hAB w.property
    rw [wordCoxeter_append,mul_assoc,hvadd _ huB,
      hvadd _ ((coxeterParabolic M b.2.1).mul_mem huB hwB)]
    exact Nat.add_le_add_left (humin w) _
  · rw [ha,hb,wordArtin_append,mul_assoc]

lemma liftedFace_antisymm (M : CoxeterMatrix S) {a b : LiftedCell M}
    (hab : LiftedFace M a b) (hba : LiftedFace M b a) : a=b := by
  obtain ⟨hAB,u,hu,hur,humin,ha⟩ := hab
  have htype : a.2.1=b.2.1 := hAB.antisymm hba.1
  have humem : wordCoxeter M u ∈ coxeterParabolic M a.2.1 := by
    rw [htype]
    exact wordCoxeter_mem_parabolic M b.2.1 u hu
  have hh := humin ⟨(wordCoxeter M u)⁻¹,(coxeterParabolic M a.2.1).inv_mem humem⟩
  simp only [mul_inv_cancel,M.toCoxeterSystem.length_one] at hh
  have hulen : u.length=0 := by omega
  have hunil := List.eq_nil_of_length_eq_zero hulen
  rw [hunil] at ha
  simp only [wordArtin,List.map_nil,List.prod_nil,mul_one] at ha
  exact Prod.ext ha (Subtype.ext htype)

lemma lifted_le_iff_face (M : CoxeterMatrix S) (a b : LiftedCell M) :
    a ≤ b ↔ LiftedFace M a b := by
  constructor
  · intro h
    induction h with
    | refl => exact liftedFace_refl M _
    | tail h hstep ih => exact liftedFace_trans M ih hstep
  · exact Relation.ReflTransGen.single

lemma lifted_le_antisymm (M : CoxeterMatrix S) {a b : LiftedCell M}
    (hab : a ≤ b) (hba : b ≤ a) : a=b :=
  liftedFace_antisymm M ((lifted_le_iff_face M a b).mp hab) ((lifted_le_iff_face M b a).mp hba)

def cellToDeligne (M : CoxeterMatrix S) (a : LiftedCell M) : Deligne M :=
  ⟨(a.2.1,rightCoset M a.2.1 a.1⁻¹),a.2.property,⟨a.1⁻¹,rfl⟩⟩

lemma cellToDeligne_monotone (M : CoxeterMatrix S) : Monotone (cellToDeligne M) := by
  intro a b hab
  obtain ⟨hAB,u,hu,hur,humin,ha⟩ := (lifted_le_iff_face M a b).mp hab
  change a.2.1 ⊆ b.2.1 ∧ rightCoset M a.2.1 a.1⁻¹ ⊆ rightCoset M b.2.1 b.1⁻¹
  refine ⟨hAB,?_⟩
  intro g hg
  change g*(a.1⁻¹)⁻¹ ∈ artinParabolic M a.2.1 at hg
  change g*(b.1⁻¹)⁻¹ ∈ artinParabolic M b.2.1
  simp only [inv_inv] at hg ⊢
  have hmem := artinParabolic_mono M hAB hg
  have huA := wordArtin_mem_parabolic M b.2.1 u hu
  have hprod := (artinParabolic M b.2.1).mul_mem hmem ((artinParabolic M b.2.1).inv_mem huA)
  simpa only [ha,mul_assoc,mul_inv_cancel,mul_one] using hprod

def cellToDeligneOrderHom (M : CoxeterMatrix S) : LiftedCell M →o Deligne M :=
  ⟨cellToDeligne M,cellToDeligne_monotone M⟩

end HarmonicArtin

end OAI
