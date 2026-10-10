import Mathlib
import OAI.Topology.ArtinGroups.Geometry.RootPair

namespace OAI

namespace HarmonicArtin.Geometric
open HarmonicArtin.CoxeterExchange
open scoped BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S W : Type*} [Fintype S] [DecidableEq S] [Group W]
  {M : CoxeterMatrix S} (cs : CoxeterSystem M W)

lemma rootRow_orthogonal_word (a : S) (u : List S) (x : S → ℝ)
    (hu : ∀ i∈u,cartan M a i=0) :
    rootRow M a (representation cs (cs.wordProd u) x)=rootRow M a x := by
  induction u with
  | nil => simp
  | cons i u ih =>
    have hao : cartan M a i=0 := hu i (by simp)
    have hu' : ∀ j∈u,cartan M a j=0 := fun j hj => hu j (by simp [hj])
    rw [CoxeterSystem.wordProd_cons,map_mul,LinearEquiv.mul_apply,representation_simple,
      simpleReflection_apply,map_sub,map_smul,rootRow_single,hao,smul_zero,sub_zero,ih hu']

theorem orthogonal_ascent_block (p : S → ℝ) (hp : ∀ i,0 < rootRow M i p)
    (u : List S) (hu : u.Nodup)
    (ho : ∀ i∈u,∀ j∈u,i≠j → cartan M i j=0)
    (w : W) (hw : ∀ i∈u,cs.length (cs.simple i*w)=cs.length w+1) :
    cs.length (cs.wordProd u*w)=u.length+cs.length w := by
  induction u with
  | nil => simp
  | cons i u ih =>
    obtain ⟨hin,hn⟩ := List.nodup_cons.mp hu
    have ho' : ∀ a∈u,∀ b∈u,a≠b → cartan M a b=0 :=
      fun a ha b hb => ho a (by simp [ha]) b (by simp [hb])
    have hw' : ∀ a∈u,cs.length (cs.simple a*w)=cs.length w+1 :=
      fun a ha => hw a (by simp [ha])
    have hi : 0 < rootRow M i (representation cs w p) :=
      (rootRow_pos_iff_left_ascent cs p hp w i).mpr (hw i (by simp))
    have hi' : 0 < rootRow M i (representation cs (cs.wordProd u*w) p) := by
      rw [map_mul,LinearEquiv.mul_apply,rootRow_orthogonal_word]
      · exact hi
      · intro j hj
        exact ho i (by simp) j (by simp [hj]) (fun he => hin (he ▸ hj))
    have ha := (rootRow_pos_iff_left_ascent cs p hp (cs.wordProd u*w) i).mp hi'
    rw [CoxeterSystem.wordProd_cons,mul_assoc,ha,ih hn ho' hw',List.length_cons]
    omega

end HarmonicArtin.Geometric

end OAI
