import OAI.RingTheory.BassTrace.ModuleK0

namespace OAI

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral
noncomputable section

namespace BassTrace.RightProjective

universe u v

theorem bassTraceModules {G : Type u} [_root_.Group G]
    (x : ModuleK0.{u,v} (MonoidAlgebra ℂ G)) (g : G) (hg : ¬IsOfFinOrder g) :
    HattoriStallings x (ConjClasses.mk g)=0 :=
  K0.bassTraceK0 (presentation x) g hg

theorem bassTraceModules_support {G : Type u} [_root_.Group G]
    (x : ModuleK0.{u,v} (MonoidAlgebra ℂ G)) :
    ↑(HattoriStallings x).support ⊆ {c | ∃g : G,IsOfFinOrder g ∧ ConjClasses.mk g=c} :=
  K0.bassTraceK0_support (presentation x)

theorem bassTraceModules_vanishing_and_support {G : Type u} [_root_.Group G]
    (x : ModuleK0.{u,v} (MonoidAlgebra ℂ G)) :
    (∀ g : G, ¬IsOfFinOrder g → HattoriStallings x (ConjClasses.mk g) = 0) ∧
      ↑(HattoriStallings x).support ⊆
        {c | ∃ g : G, IsOfFinOrder g ∧ ConjClasses.mk g = c} :=
  ⟨fun g hg => bassTraceModules x g hg, bassTraceModules_support x⟩

end BassTrace.RightProjective

end

end OAI
