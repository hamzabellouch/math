import Mathlib
import OAI.RingTheory.Multiplicity.CartierTowerDevissage
import OAI.RingTheory.Multiplicity.ReesRootLayerTotal
import OAI.RingTheory.Multiplicity.ReesRootPowerPath

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
open ProductSourceCover
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I)
  (F : CochainComplex (ModuleCat.{u} R) ℤ) (h s : ℕ)
  (hd : ∀ p : ℤ, (F.d p (p+1)).hom.range ≤ I^s • (⊤ : Submodule R (F.X (p+1))))
  (m : Fin n → ℤ) (hgen : Ideal.span (Set.range z)=I)
  (hflat : ∀ p,Module.Flat R (F.X p))

include hgen hflat in
lemma enlargedStep_total_mono (t : ℕ) :
    Mono (total.map (enlargedStep I z hz F h s hd m 1 t) (.up ℤ)) :=
  (BicomplexTotal.total_shortExact _
    (enlargedLayerShortComplex_exact I z hz F h s hd (twistSequence m 1 t) hgen hflat)).mono_f

include hgen hflat in
lemma enlargedStep_cokernel_property (P : ObjectProperty (ModuleCat.{u} R)) [P.IsSerreClass]
    (t : ℕ) (i : ℤ)
    (hl : P (((layerAt I z hz F h s hd (twistSequence m 1 t)).total (.up ℤ)).homology i)) :
    P ((cokernel (total.map (enlargedStep I z hz F h s hd m 1 t) (.up ℤ))).homology i) :=
  cokernel_homology_property_of_shortExact P
    (BicomplexTotal.total_shortExact _
      (enlargedLayerShortComplex_exact I z hz F h s hd (twistSequence m 1 t) hgen hflat)) i hl

include hgen hflat in
lemma enlargedPath_total_mono (M : ℕ) :
    Mono (total.map (enlargedPath I z hz F h s hd m 1 M) (.up ℤ)) := by
  have hh := TotalGhost.towerPath_mono
    (X:=fun t => (enlargedAt I z hz F h s hd (twistSequence m 1 t)).total (.up ℤ))
    (fun t => total.map (enlargedStep I z hz F h s hd m 1 t) (.up ℤ))
    (enlargedStep_total_mono I z hz F h s hd m hgen hflat) M
  have he := TotalGhost.towerPath_map
    (X:=fun t => enlargedAt I z hz F h s hd (twistSequence m 1 t))
    (enlargedStep I z hz F h s hd m 1) (BicomplexTotal.functor (R:=R)) M
  change TotalGhost.towerPath
    (X:=fun t => (enlargedAt I z hz F h s hd (twistSequence m 1 t)).total (.up ℤ))
    (fun t => total.map (enlargedStep I z hz F h s hd m 1 t) (.up ℤ)) M =
      total.map (enlargedPath I z hz F h s hd m 1 M) (.up ℤ) at he
  rwa [he] at hh

include hgen hflat in
lemma enlargedPath_cokernel_property (P : ObjectProperty (ModuleCat.{u} R)) [P.IsSerreClass]
    (M : ℕ) (i : ℤ)
    (hl : ∀ t,t<M → P (((layerAt I z hz F h s hd (twistSequence m 1 t)).total (.up ℤ)).homology i)) :
    P ((cokernel (total.map (enlargedPath I z hz F h s hd m 1 M) (.up ℤ))).homology i) := by
  have hh := TotalGhost.towerPath_cokernel_property
    (X:=fun t => (enlargedAt I z hz F h s hd (twistSequence m 1 t)).total (.up ℤ))
    (fun t => total.map (enlargedStep I z hz F h s hd m 1 t) (.up ℤ))
    (enlargedStep_total_mono I z hz F h s hd m hgen hflat) P M i
    (fun t ht => enlargedStep_cokernel_property I z hz F h s hd m hgen hflat P t i (hl t ht))
  have he := TotalGhost.towerPath_map
    (X:=fun t => enlargedAt I z hz F h s hd (twistSequence m 1 t))
    (enlargedStep I z hz F h s hd m 1) (BicomplexTotal.functor (R:=R)) M
  change TotalGhost.towerPath
    (X:=fun t => (enlargedAt I z hz F h s hd (twistSequence m 1 t)).total (.up ℤ))
    (fun t => total.map (enlargedStep I z hz F h s hd m 1 t) (.up ℤ)) M =
      total.map (enlargedPath I z hz F h s hd m 1 M) (.up ℤ) at he
  rwa [he] at hh

variable [LinearOrder (Chart n)] (ell : TorsionLength I) (hds : ell.DirectSumZero)
  (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
  (ha : ∀ a : ℕ,0<a → ell.value (ModuleCat.of R
    (R ⧸ Ideal.span (Set.range (fun i => z i^a))))=a^(n+1) • ell.value (ModuleCat.of R (R ⧸ I)))
  (b : ℤ → ℕ) (B : ∀ p,Module.Basis (Fin (b p)) R (F.X p))
  (hp : ∀ p,Module.Projective R (F.X p)) (hfin : ∀ p,Module.Finite R (F.X p))
  (hb : ∀ p,p < -(h:ℤ) ∨ 0<p → IsZero (F.X p))
  (hac : ∀ k,((baseChangeFunctor R (Localization.Away (z k))).mapHomologicalComplex _ |>.obj F).Acyclic)

include hgen hflat hds hmu ha B hp hfin hb hac in
 
theorem enlargedAtTotal_finite (i : ℤ) :
    ell.finiteClass (((enlargedAt I z hz F h s hd m).total (.up ℤ)).homology i) := by
  obtain ⟨M,hM,hzero⟩ := uniform_unit_nilpotence I z hz F h s hd hgen hp hfin hflat hb hac
  have := enlargedPath_total_mono I z hz F h s hd m hgen hflat M
  apply homology_target_property_of_zero ell.finiteClass
    (total.map (enlargedPath I z hz F h s hd m 1 M) (.up ℤ)) i (hzero m i)
  apply enlargedPath_cokernel_property I z hz F h s hd m hgen hflat
  intro t ht
  exact layerAtTotal_finite I z hz _ hgen ell hds hmu ha F h s hd b B hflat hb i

 
def rootAmbient (s : ℕ) (r : Fin n → ℤ) (l : ℤ) : Fin n → ℤ :=
  baseTwist (n+1) s (fun j => l-1-r j)

omit [LinearOrder (Chart n)] in
lemma twistSequence_rootAmbient (s : ℕ) (r : Fin n → ℤ) (l : ℤ) (M : ℕ) :
    twistSequence (rootAmbient s r l) 1 M = rootAmbient s r (l+M) := by
  funext j
  simp only [twistSequence_apply,one_mul,rootAmbient,baseTwist]
  ring

include hgen hflat hds hmu ha B hp hfin hac in
 
theorem rootTotal_positive_degree (r : Fin n → ℤ) (hr : RootPositions n s r)
    (hb : ∀ p,p < -(n+1:ℤ) ∨ 0<p → IsZero (F.X p)) (i : ℤ) (hi : 0 < i) :
    ell.zeroClass (((enlargedAt I z hz F (n+1) s hd (rootAmbient s r 0)).total (.up ℤ)).homology i) := by
  obtain ⟨M,hM,hzero⟩ := uniform_unit_nilpotence I z hz F (n+1) s hd hgen hp hfin hflat hb hac
  have := enlargedPath_total_mono I z hz F (n+1) s hd (rootAmbient s r 0) hgen hflat M
  apply homology_target_property_of_zero ell.zeroClass
    (total.map (enlargedPath I z hz F (n+1) s hd (rootAmbient s r 0) 1 M) (.up ℤ)) i (hzero _ i)
  apply enlargedPath_cokernel_property I z hz F (n+1) s hd _ hgen hflat
  intro t ht
  rw [twistSequence_rootAmbient,zero_add]
  exact rootLayerAtTotal_nonnegative I z hz hgen ell hds hmu ha F s hd b B hflat r hr hb t
    (Nat.cast_nonneg _) i hi

include hgen hflat hds hmu ha B hp hfin hac in
 

theorem rootTotal_negative_degree (r : Fin n → ℤ) (hr : RootPositions n s r)
    (hb : ∀ p,p < -(n+1:ℤ) ∨ 0<p → IsZero (F.X p)) (i : ℤ) (hi : i < 0) :
    ell.zeroClass (((enlargedAt I z hz F (n+1) s hd (rootAmbient s r 0)).total (.up ℤ)).homology i) := by
  obtain ⟨M,hM,hzero⟩ := uniform_unit_nilpotence I z hz F (n+1) s hd hgen hp hfin hflat hb hac
  have := enlargedPath_total_mono I z hz F (n+1) s hd (rootAmbient s r (-(M:ℤ))) hgen hflat M
  have hh := homology_source_property_of_zero ell.zeroClass
    (total.map (enlargedPath I z hz F (n+1) s hd (rootAmbient s r (-(M:ℤ))) 1 M) (.up ℤ)) i
    (hzero _ i) (enlargedPath_cokernel_property I z hz F (n+1) s hd _ hgen hflat ell.zeroClass M (i-1) (by
      intro t ht
      rw [twistSequence_rootAmbient]
      exact rootLayerAtTotal_negative I z hz hgen ell hds hmu ha F s hd b B hflat r hr hb
        (-(M:ℤ)+t) (by omega) (i-1) (by omega)))
  change ell.zeroClass (((enlargedAt I z hz F (n+1) s hd
    (twistSequence (rootAmbient s r (-(M:ℤ))) 1 M)).total (.up ℤ)).homology i) at hh
  simpa only [twistSequence_rootAmbient,neg_add_cancel] using hh
end Lech.ReesRoot

end

end OAI
