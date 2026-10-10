import Mathlib
import OAI.Topology.ArtinGroups.Coxeter.WeakPrefix

namespace OAI

namespace HarmonicArtin.CoxeterExchange
attribute [local instance] Classical.decEq Classical.propDecidable
variable {B W:Type*} [Group W] [Fintype B] {M:CoxeterMatrix B} (cs:CoxeterSystem M W)

omit [Fintype B] in
lemma common_weakPrefix_maximal_remove (a b g:W)
    (hmax:∀x:W,WeakPrefix cs x a→WeakPrefix cs x b→cs.length x≤cs.length g)
    (s:B) (hsa:WeakPrefix cs (cs.simple s) a) (hsb:WeakPrefix cs (cs.simple s) b)
    (hsg:WeakPrefix cs (cs.simple s) g) :
    ∀x:W,WeakPrefix cs x (cs.simple s*a)→WeakPrefix cs x (cs.simple s*b)→
      cs.length x≤cs.length (cs.simple s*g) := by
  intro x hxa hxb
  obtain ⟨hxa',hl⟩:=weakPrefix_left_add cs s hsa hxa
  have hxb':=(weakPrefix_left_add cs s hsb hxb).1
  have hh:=hmax _ hxa' hxb'
  have hg:=(weakPrefix_simple_iff cs s g).mp hsg
  omega

theorem maximal_common_weakPrefix_greatest (a b g:W)
    (hga:WeakPrefix cs g a) (hgb:WeakPrefix cs g b)
    (hmax:∀x:W,WeakPrefix cs x a→WeakPrefix cs x b→cs.length x≤cs.length g) :
    ∀e:W,WeakPrefix cs e a→WeakPrefix cs e b→WeakPrefix cs e g := by
  induction a using (measure cs.length).wf.induction generalizing b g with
  | h a ih=>
    intro e hea heb
    by_cases he:e=1
    · rw [he];exact weakPrefix_one cs g
    obtain ⟨s,hse⟩:=exists_simple_prefix cs he
    have hsa:=weakPrefix_trans cs hse hea
    have hsb:=weakPrefix_trans cs hse heb
    have hsg:WeakPrefix cs (cs.simple s) g:=by
      have hg:g≠1:=by
        intro hg
        have hh:=hmax _ hsa hsb
        rw [hg,cs.length_simple,cs.length_one] at hh
        omega
      obtain ⟨t,htg⟩:=exists_simple_prefix cs hg
      by_cases hts:t=s
      · simpa only [hts] using htg
      have hta:=weakPrefix_trans cs htg hga
      have htb:=weakPrefix_trans cs htg hgb
      let d:=cs.wordProd (altList t s (M t s))
      obtain ⟨hda,htd,hsd⟩:=simple_pair_prefix cs t s hts hta hsa
      have hdb:WeakPrefix cs d b:=(simple_pair_prefix cs t s hts htb hsb).1
      have hga':WeakPrefix cs (cs.simple t*g) (cs.simple t*a):=
        (weakPrefix_left_remove cs t htg hta).mpr hga
      have hgb':WeakPrefix cs (cs.simple t*g) (cs.simple t*b):=
        (weakPrefix_left_remove cs t htg htb).mpr hgb
      have hmax':=common_weakPrefix_maximal_remove cs a b g hmax t hta htb htg
      have hlt:cs.length (cs.simple t*a)<cs.length a:=by
        have hh:=(weakPrefix_simple_iff cs t a).mp hta;omega
      have hda':WeakPrefix cs (cs.simple t*d) (cs.simple t*a):=
        (weakPrefix_left_remove cs t htd hta).mpr hda
      have hdb':WeakPrefix cs (cs.simple t*d) (cs.simple t*b):=
        (weakPrefix_left_remove cs t htd htb).mpr hdb
      have hdg':=ih (cs.simple t*a) hlt (cs.simple t*b) (cs.simple t*g) hga' hgb' hmax' (cs.simple t*d) hda' hdb'
      have hdg:WeakPrefix cs d g:=(weakPrefix_left_remove cs t htd htg).mp hdg'
      exact weakPrefix_trans cs hsd hdg
    have hea':WeakPrefix cs (cs.simple s*e) (cs.simple s*a):=
      (weakPrefix_left_remove cs s hse hsa).mpr hea
    have heb':WeakPrefix cs (cs.simple s*e) (cs.simple s*b):=
      (weakPrefix_left_remove cs s hse hsb).mpr heb
    have hga':WeakPrefix cs (cs.simple s*g) (cs.simple s*a):=
      (weakPrefix_left_remove cs s hsg hsa).mpr hga
    have hgb':WeakPrefix cs (cs.simple s*g) (cs.simple s*b):=
      (weakPrefix_left_remove cs s hsg hsb).mpr hgb
    have hmax':=common_weakPrefix_maximal_remove cs a b g hmax s hsa hsb hsg
    have hlt:cs.length (cs.simple s*a)<cs.length a:=by
      have hh:=(weakPrefix_simple_iff cs s a).mp hsa;omega
    have heg':=ih (cs.simple s*a) hlt (cs.simple s*b) (cs.simple s*g) hga' hgb' hmax' (cs.simple s*e) hea' heb'
    exact (weakPrefix_left_remove cs s hse hsg).mp heg'

theorem exists_greatest_common_weakPrefix (a b:W) :
    ∃g:W,WeakPrefix cs g a ∧ WeakPrefix cs g b ∧
      ∀e:W,WeakPrefix cs e a→WeakPrefix cs e b→WeakPrefix cs e g := by
  let P:ℕ→Prop:=fun n=>∃g:W,WeakPrefix cs g a ∧ WeakPrefix cs g b ∧ cs.length g=n
  have hP:P 0:=⟨1,weakPrefix_one cs a,weakPrefix_one cs b,cs.length_one⟩
  obtain ⟨g,hga,hgb,hlen⟩:=Nat.findGreatest_spec (Nat.zero_le (cs.length a)) hP
  refine ⟨g,hga,hgb,maximal_common_weakPrefix_greatest cs a b g hga hgb ?_⟩
  intro x hxa hxb
  rw [hlen]
  exact Nat.le_findGreatest (weakPrefix_length cs hxa) ⟨x,hxa,hxb,rfl⟩

end HarmonicArtin.CoxeterExchange

end OAI
