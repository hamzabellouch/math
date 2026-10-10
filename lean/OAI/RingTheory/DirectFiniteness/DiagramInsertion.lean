import OAI.RingTheory.DirectFiniteness.WordCycles

namespace OAI

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.Planar
open Equiv Equiv.Perm
variable {V F A B : Type} [AddCommGroup A] [AddCommGroup B]
variable {Inc : V → F → Prop} {ι : V → F → (A →+ B)}
variable {f₀ : F} {w : List (F × A)}

theorem OpenDiagram.insertBlock (D : OpenDiagram Inc ι f₀ w)
    (pre post : List D.Edge) (hboundary : D.boundary = pre ++ post)
    (r : List (F × A)) (v : V) (hinc : ∀ t ∈ r, Inc v t.1)
    (hsum : (r.map (fun t => ι v t.1 t.2)).sum = 0) :
    Nonempty (OpenDiagram Inc ι f₀
      (pre.map (fun x => (D.balanced.whiteLabel x, D.balanced.weight x)) ++ r ++
        post.map (fun x => (D.balanced.whiteLabel x, D.balanced.weight x)))) := by
  classical
  by_cases hr : r = []
  · subst r
    have hw : w = pre.map (fun x => (D.balanced.whiteLabel x, D.balanced.weight x)) ++
        [] ++ post.map (fun x => (D.balanced.whiteLabel x, D.balanced.weight x)) := by
      exact D.word.symm.trans (by rw [hboundary, List.map_append, List.append_nil])
    exact ⟨hw ▸ D⟩
  let p := (List.finRange r.length).formPerm
  let W := wordWheel r v hinc hsum
  let T := D.ribbon.sum (Ribbon.wheel p)
  let E := D.balanced.sumZero W
  let f : D.Edge → D.Edge ⊕ (Fin r.length ⊕ Fin r.length) := Sum.inl
  let g : Fin r.length → D.Edge ⊕ (Fin r.length ⊕ Fin r.length) := Sum.inr ∘ Sum.inl
  let Q := (List.finRange r.length).map g
  let M := (post ++ D.anchor :: pre).map f
  have hqn : Q ≠ [] := by
    intro he
    have hh : r.length = 0 := by simpa only [Q, List.length_map, List.length_finRange, List.length_nil] using congrArg List.length he
    exact hr (List.length_eq_zero_iff.mp hh)
  have hmn : M ≠ [] := by simp [M]
  obtain ⟨a, l, hqa⟩ := List.exists_cons_of_ne_nil hqn
  obtain ⟨b, m, hmb⟩ := List.exists_cons_of_ne_nil hmn
  have hnd₀ : ((D.anchor :: pre) ++ post).Nodup := by
    simpa only [hboundary, List.cons_append] using D.nodup
  have hrot₀ : Follows D.ribbon.black ((D.anchor :: pre) ++ post) := by
    simpa only [hboundary, List.cons_append] using D.rotation
  have hndM : M.Nodup := (List.nodup_append_comm.mp hnd₀).map Sum.inl_injective
  have hndQ : Q.Nodup := (List.nodup_finRange _).map (Sum.inr_injective.comp Sum.inl_injective)
  have hM : Follows T.black M := by
    exact (hrot₀.append_rotate hnd₀).map_sum_left
  have hQ : Follows T.black Q := by
    have h : Follows (Ribbon.wheel p).black ((List.finRange r.length).map Sum.inl) :=
      (follows_formPerm (List.finRange r.length)).map_sum_left
    simpa only [List.map_map, T, Ribbon.sum, Q, g] using h.map_sum_right (p := D.ribbon.black)
  have hdis : List.Disjoint Q M := by
    intro x hx hy
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    obtain ⟨j, _, hj⟩ := List.mem_map.mp hy
    exact Sum.inl_ne_inr (show (Sum.inl j : D.Edge ⊕ (Fin r.length ⊕ Fin r.length)) = Sum.inr (Sum.inl i) from hj)
  have hnd : (Q ++ M).Nodup := List.Nodup.append hndQ hndM hdis
  have hac : a ∈ Q := by rw [hqa]; simp
  have hbc : b ∈ M := by rw [hmb]; simp
  have hcomp : ¬ T.components.r a b := by
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hac
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hbc
    rw [Ribbon.sum_components]
    exact fun h => sumSetoid_cross _ _ j (Sum.inl i)
      ((sumSetoid D.ribbon.components (Ribbon.wheel p).components).iseqv.symm h)
  have hal : E.blackLabel a = none := by
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hac
    rfl
  have hbl : E.blackLabel b = none := by
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hbc
    apply (D.exposed j).mpr
    simpa only [hboundary, List.mem_append, List.mem_cons, or_assoc, or_left_comm, or_comm] using hj
  let S := T.swapBlack a b
  let Z := E.joinBlack a b (T.not_blackCycle_of_not_component hcomp) (hal.trans hbl.symm)
  have hrot : Follows S.black (Q ++ M) := by
    simp only [hqa, hmb] at hQ hM hdis ⊢
    exact hQ.merge hM hdis
  have hrot' : Follows S.black (f D.anchor :: (pre.map f ++ Q ++ post.map f)) := by
    have hh : Follows S.black ((Q ++ post.map f) ++ (f D.anchor :: pre.map f)) := by
      simpa only [M, List.map_append, List.map_cons, List.append_assoc] using hrot
    have hn : ((Q ++ post.map f) ++ (f D.anchor :: pre.map f)).Nodup := by
      simpa only [M, List.map_append, List.map_cons, List.append_assoc] using hnd
    simpa only [List.cons_append, List.append_assoc] using hh.append_rotate hn
  have hnd' : (f D.anchor :: (pre.map f ++ Q ++ post.map f)).Nodup := by
    have hn : ((Q ++ post.map f) ++ (f D.anchor :: pre.map f)).Nodup := by
      simpa only [M, List.map_append, List.map_cons, List.append_assoc] using hnd
    simpa only [List.cons_append, List.append_assoc] using List.nodup_append_comm.mp hn
  refine ⟨{
    Edge := D.Edge ⊕ (Fin r.length ⊕ Fin r.length)
    fintype := inferInstance
    ribbon := S
    balanced := Z
    planar := T.genusZero_swapBlack_merge (D.ribbon.genusZero_sum (Ribbon.wheel p) D.planar
      (Ribbon.genusZero_wheel p)) a b hcomp
    anchor := f D.anchor
    boundary := pre.map f ++ Q ++ post.map f
    nodup := hnd'
    rotation := hrot'
    exposed := ?_
    anchor_weight := D.anchor_weight
    anchor_label := D.anchor_label
    word := ?_ }⟩
  · rintro (x | (i | i))
    · change D.balanced.blackLabel x = none ↔ _
      rw [D.exposed, hboundary]
      simp [f, Q, g, List.mem_map, Function.comp_def, List.mem_append, List.mem_cons]
    · change (none : Option V) = none ↔ _
      simp [f, Q, g, List.mem_map, Function.comp_def]
    · change (some v : Option V) = none ↔ _
      simp [f, Q, g, List.mem_map, Function.comp_def]
  · change (pre.map f ++ Q ++ post.map f).map
        (fun x => (E.whiteLabel x, E.weight x)) = _
    simp only [List.map_append, List.map_map]
    congr 2
    dsimp only [Q]
    rw [List.map_map]
    change ((List.finRange r.length).map (fun i => r.get i)) = r
    exact List.map_get_finRange r

end KaplanskyCounterexample.Planar

end

end OAI
