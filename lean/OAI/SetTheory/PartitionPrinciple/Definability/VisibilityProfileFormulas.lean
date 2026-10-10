import OAI.SetTheory.PartitionPrinciple.Forcing.GroundRepresentedDomainConditions

namespace OAI

namespace PartitionPilot.Forcing

section
open SetRealization SetFormula
universe u

def stageOneRawProfile (M : TransitiveGround.{u}) (P r lower nodes nodeOrder visibility E bu aw : ZFSet.{u}) : Prop :=
  ∀ v ∈ nodes, ZFSet.pair E v ∈ nodeOrder →
    ∃ V ∈ M.sets, ZFSet.pair v V ∈ visibility ∧
      stageOneRawForces M P r lower refinementProfileFormula ![bu, aw, V]

def stageOneRawCompatibility (M : TransitiveGround.{u}) (P r lower visibility maps C idx bu aw : ZFSet.{u}) : Prop :=
  ∃ V ∈ M.sets, ∃ D ∈ M.sets, ZFSet.pair C V ∈ visibility ∧ ZFSet.pair idx D ∈ maps ∧
    stageOneRawForces M P r lower refinementCompatibilityFormula ![aw, V, bu, D]

namespace SetFormula

def stageOneProfileAt {n : Nat} (P r lower nodes nodeOrder visibility E bu aw : Fin n) : SetFormula n :=
  .all (imp (.mem 0 nodes.succ)
    (imp (BoundedFormula.pairMembershipFormula E.succ 0 nodeOrder.succ).toFormula
      (ex (.conj (BoundedFormula.pairMembershipFormula 1 0 visibility.succ.succ).toFormula
        (stageOneForcingAt refinementProfileFormula lower.succ.succ P.succ.succ r.succ.succ
          (extend bu.succ.succ (extend aw.succ.succ (extend 0 Fin.elim0))))))))

def stageOneCompatibilityAt {n : Nat} (P r lower visibility maps C idx bu aw : Fin n) : SetFormula n :=
  ex (ex (.conj (BoundedFormula.pairMembershipFormula C.succ.succ 1 visibility.succ.succ).toFormula
    (.conj (BoundedFormula.pairMembershipFormula idx.succ.succ 0 maps.succ.succ).toFormula
      (stageOneForcingAt refinementCompatibilityFormula lower.succ.succ P.succ.succ r.succ.succ
        (extend aw.succ.succ (extend 1 (extend bu.succ.succ (extend 0 Fin.elim0))))))))

end SetFormula

private theorem map_three {α β : Type*} (f : α → β) (a b c : α) :
    (fun j : Fin 3 => f ((extend a (extend b (extend c Fin.elim0))) j)) = ![f a, f b, f c] := by
  funext j
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))) j

private theorem map_four {α β : Type*} (f : α → β) (a b c d : α) :
    (fun j : Fin 4 => f ((extend a (extend b (extend c (extend d Fin.elim0)))) j)) = ![f a, f b, f c, f d] := by
  funext j
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))) j

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_stageOnePairLookup {n : Nat} (x y R : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (BoundedFormula.pairMembershipFormula x y R).toFormula env ↔
      ZFSet.pair (env x) (env y) ∈ env R :=
  (BoundedFormula.realize_toFormula M _ env members).trans (BoundedFormula.truth_pairMembershipFormula x y R env)

theorem realize_stageOneProfileAt {n : Nat} (P r lower nodes nodeOrder visibility E bu aw : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (stageOneProfileAt P r lower nodes nodeOrder visibility E bu aw) env ↔
      stageOneRawProfile M (env P) (env r) (env lower) (env nodes) (env nodeOrder) (env visibility)
        (env E) (env bu) (env aw) := by
  rw [stageOneProfileAt]
  change (∀ v ∈ M.sets, Realize M.sets _ (extend v env)) ↔ _
  constructor
  · intro h v hv below
    have hvM := M.transitive (members nodes) hv
    have first := (realize_imp M.sets _ _ _).1 (h v hvM) hv
    have selected := (realize_imp M.sets _ _ _).1 first
      ((M.realize_stageOnePairLookup E.succ 0 nodeOrder.succ _ (Fin.cases hvM members)).2 below)
    obtain ⟨V, hV, entry, forced⟩ := (realize_ex M.sets _ _).1 selected
    refine ⟨V, hV, (M.realize_stageOnePairLookup 1 0 visibility.succ.succ _
      (Fin.cases hV (Fin.cases hvM members))).1 entry, ?_⟩
    have value := (M.realize_stageOneForcingAt _ _ _ _ _ _).1 forced
    rw [map_three] at value
    exact value
  · intro h v hvM
    apply (realize_imp M.sets _ _ _).2
    intro hv
    apply (realize_imp M.sets _ _ _).2
    intro below
    have relation := (M.realize_stageOnePairLookup E.succ 0 nodeOrder.succ _ (Fin.cases hvM members)).1 below
    obtain ⟨V, hV, entry, forced⟩ := h v hv relation
    apply (realize_ex M.sets _ _).2
    refine ⟨V, hV, (M.realize_stageOnePairLookup 1 0 visibility.succ.succ _
      (Fin.cases hV (Fin.cases hvM members))).2 entry, ?_⟩
    apply (M.realize_stageOneForcingAt _ _ _ _ _ _).2
    rw [map_three]
    exact forced

theorem realize_stageOneCompatibilityAt {n : Nat} (P r lower visibility maps C idx bu aw : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (stageOneCompatibilityAt P r lower visibility maps C idx bu aw) env ↔
      stageOneRawCompatibility M (env P) (env r) (env lower) (env visibility) (env maps)
        (env C) (env idx) (env bu) (env aw) := by
  rw [stageOneCompatibilityAt, realize_ex]
  constructor
  · rintro ⟨V, hV, body⟩
    obtain ⟨D, hD, visible, mapped, forced⟩ := (realize_ex M.sets _ _).1 body
    refine ⟨V, hV, D, hD,
      (M.realize_stageOnePairLookup C.succ.succ 1 visibility.succ.succ _ (Fin.cases hD (Fin.cases hV members))).1 visible,
      (M.realize_stageOnePairLookup idx.succ.succ 0 maps.succ.succ _ (Fin.cases hD (Fin.cases hV members))).1 mapped, ?_⟩
    have value := (M.realize_stageOneForcingAt _ _ _ _ _ _).1 forced
    rw [map_four] at value
    exact value
  · rintro ⟨V, hV, D, hD, visible, mapped, forced⟩
    refine ⟨V, hV, ?_⟩
    apply (realize_ex M.sets _ _).2
    refine ⟨D, hD,
      (M.realize_stageOnePairLookup C.succ.succ 1 visibility.succ.succ _ (Fin.cases hD (Fin.cases hV members))).2 visible,
      (M.realize_stageOnePairLookup idx.succ.succ 0 maps.succ.succ _ (Fin.cases hD (Fin.cases hV members))).2 mapped, ?_⟩
    apply (M.realize_stageOneForcingAt _ _ _ _ _ _).2
    rw [map_four]
    exact forced

end TransitiveGround

end

open SetFormula
universe u

namespace SetFormula
def supportedEqualitySequenceFormula : SetFormula 6 :=
  .conj (BoundedFormula.functionFormula 0 1 2).toFormula
    (.all (imp (.mem 0 1) (.all (imp (.mem 0 3)
      (imp (BoundedFormula.pairMembershipFormula 1 0 4).toFormula
        (.conj (BoundedFormula.pairMembershipFormula 1 0 5).toFormula
          (BoundedFormula.pairMembershipFormula 0 7 6).toFormula))))))
end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_supportedEqualitySequenceFormula (env : Fin 6 → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets supportedEqualitySequenceFormula env ↔
      ZFSet.IsFunc (env 0) (env 1) (env 2) ∧
      ∀ v ∈ env 0, ∀ tau ∈ env 1, ZFSet.pair v tau ∈ env 2 →
        ZFSet.pair v tau ∈ env 3 ∧ ZFSet.pair tau (env 5) ∈ env 4 := by
  have function := (BoundedFormula.realize_toFormula M
    (BoundedFormula.functionFormula 0 1 2) env members).trans
      (BoundedFormula.truth_functionFormula 0 1 2 env)
  constructor
  · intro realized
    refine ⟨function.1 realized.1, ?_⟩
    intro v hv tau ht entry
    have hvM := M.transitive (members 0) hv
    have htM := M.transitive (members 1) ht
    have atNode := (realize_imp M.sets _ _ _).1 (realized.2 v hvM) hv
    have atCode := (realize_imp M.sets _ _ _).1 (atNode tau htM) ht
    have result := (realize_imp M.sets _ _ _).1 atCode
      ((M.realize_stageOnePairLookup 1 0 4 _ (Fin.cases htM (Fin.cases hvM members))).2 entry)
    exact ⟨(M.realize_stageOnePairLookup 1 0 5 _ (Fin.cases htM (Fin.cases hvM members))).1 result.1,
      (M.realize_stageOnePairLookup 0 7 6 _ (Fin.cases htM (Fin.cases hvM members))).1 result.2⟩
  · rintro ⟨isFunction, meaning⟩
    refine ⟨function.2 isFunction, ?_⟩
    intro v hvM
    apply (realize_imp M.sets _ _ _).2
    intro hv tau htM
    apply (realize_imp M.sets _ _ _).2
    intro ht
    apply (realize_imp M.sets _ _ _).2
    intro entry
    have result := meaning v hv tau ht
      ((M.realize_stageOnePairLookup 1 0 4 _ (Fin.cases htM (Fin.cases hvM members))).1 entry)
    exact ⟨(M.realize_stageOnePairLookup 1 0 5 _ (Fin.cases htM (Fin.cases hvM members))).2 result.1,
      (M.realize_stageOnePairLookup 0 7 6 _ (Fin.cases htM (Fin.cases hvM members))).2 result.2⟩

end TransitiveGround

namespace SetFormula

def visibilityProfileFormula : SetFormula 4 :=
  .all (imp (.mem 0 3) (.all (imp (BoundedFormula.pairMembershipFormula 1 0 3).toFormula
    (.conj (imp (.mem 2 0) (.mem 1 5)) (imp (.mem 1 5) (.mem 2 0))))))
end SetFormula

namespace TransitiveGround
variable (N : TransitiveGround.{u})

theorem realize_visibilityProfileFormula (env : Fin 4 → ZFSet.{u})
    (members : ∀ i, env i ∈ N.sets) :
    Realize N.sets visibilityProfileFormula env ↔
      ∀ v ∈ env 2, ∀ V ∈ N.sets, ZFSet.pair v V ∈ env 1 → (env 0 ∈ V ↔ v ∈ env 3) := by
  constructor
  · intro realized v hv V hV entry
    have hvN := N.transitive (members 2) hv
    have atNode := (realize_imp N.sets _ _ _).1 (realized v hvN) hv
    have atValue := (realize_imp N.sets _ _ _).1 (atNode V hV)
      ((N.realize_stageOnePairLookup 1 0 3 _ (Fin.cases hV (Fin.cases hvN members))).2 entry)
    exact ⟨(realize_imp N.sets _ _ _).1 atValue.1,
      (realize_imp N.sets _ _ _).1 atValue.2⟩
  · intro meaning v hvN
    apply (realize_imp N.sets _ _ _).2
    intro hv V hV
    apply (realize_imp N.sets _ _ _).2
    intro entry
    have exactProfile := meaning v hv V hV
      ((N.realize_stageOnePairLookup 1 0 3 _ (Fin.cases hV (Fin.cases hvN members))).1 entry)
    exact ⟨(realize_imp N.sets _ _ _).2 exactProfile.1,
      (realize_imp N.sets _ _ _).2 exactProfile.2⟩

end TransitiveGround

end PartitionPilot.Forcing

end OAI
