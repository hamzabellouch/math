import Mathlib

namespace OAI

namespace HarmonicArtin
lemma finsupp_mapDomain_fiber {A B M:Type*} [AddCommMonoid M]
    (f g:A →₀ M) (h:A → B) (b:B) (he:∀ a,h a=b → f a=g a) :
    f.mapDomain h b=g.mapDomain h b := by
  classical
  rw [Finsupp.mapDomain,Finsupp.mapDomain,Finsupp.sum_apply,Finsupp.sum_apply]
  rw [Finsupp.sum_of_support_subset f (Finset.subset_union_left) _ (by simp),
    Finsupp.sum_of_support_subset g (Finset.subset_union_right) _ (by simp)]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha:h a=b
  · rw [Finsupp.single_apply,Finsupp.single_apply,ite_eq_left ha,ite_eq_left ha,he a ha]
  · simp only [Finsupp.single_apply,ha,ite_false]
end HarmonicArtin

end OAI
