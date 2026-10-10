import OAI.RingTheory.DirectFiniteness.BoundarySplitting

namespace OAI

universe u_1 u_2 u_3 u_4

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.Planar
open Equiv Equiv.Perm
variable {V : Type u_1} {F : Type u_2} {A : Type u_3} {B : Type u_4} [AddCommGroup A] [AddCommGroup B]
variable {Inc : V → F → Prop} {ι : V → F → (A →+ B)} {f₀ : F} {w : List (F × A)}

theorem OpenDiagram.deleteBlock (D : OpenDiagram Inc ι f₀ w)
    (pre r post : List D.Edge) (hboundary : D.boundary = pre ++ r ++ post)
    (v : V) (hinc : ∀ x ∈ r, Inc v (D.balanced.whiteLabel x))
    (hsum : (∑ x ∈ r.toFinset, ι v (D.balanced.whiteLabel x) (D.balanced.weight x)) = 0) :
    Nonempty (OpenDiagram Inc ι f₀ ((pre ++ post).map
      (fun x => (D.balanced.whiteLabel x, D.balanced.weight x)))) := by
  classical
  cases r with
  | nil =>
    have hw : w = (pre ++ post).map (fun x => (D.balanced.whiteLabel x, D.balanced.weight x)) := by
      exact D.word.symm.trans (congrArg _ (by simpa only [List.append_nil] using hboundary))
    exact ⟨hw ▸ D⟩
  | cons a r =>
    let M := post ++ D.anchor :: pre
    have hM : M ≠ [] := by
      intro empty
      have member : D.anchor ∈ M := List.mem_append_right post (List.mem_cons_self ..)
      rw [empty] at member
      exact List.not_mem_nil member
    obtain ⟨b, m, hbm⟩ := List.exists_cons_of_ne_nil hM
    have hrot : Follows D.ribbon.black ((D.anchor :: pre) ++ ((a :: r) ++ post)) := by
      simpa only [hboundary, List.cons_append, List.append_assoc] using D.rotation
    have hnd : (((D.anchor :: pre) ++ ((a :: r) ++ post))).Nodup := by
      simpa only [hboundary, List.cons_append, List.append_assoc] using D.nodup
    have hrot' : Follows D.ribbon.black ((a :: r) ++ (b :: m)) := by
      simpa only [List.append_assoc, ← hbm] using hrot.append_rotate hnd
    have hnd' : ((a :: r) ++ (b :: m)).Nodup := by
      have hn := (List.nodup_append_comm).mp hnd
      simpa only [List.append_assoc, ← hbm] using hn
    have hmem (x : D.Edge) : x ∈ D.anchor :: D.boundary ↔ x ∈ (a :: r) ++ (b :: m) := by
      simp only [hboundary, ← hbm, M, List.mem_cons, List.mem_append]
      constructor
      · rintro (anchor | ((before | (head | tail)) | suffix))
        · exact Or.inr (Or.inr (Or.inl anchor))
        · exact Or.inr (Or.inr (Or.inr before))
        · exact Or.inl (Or.inl head)
        · exact Or.inl (Or.inr tail)
        · exact Or.inr (Or.inl suffix)
      · rintro ((head | tail) | (suffix | anchor | before))
        · exact Or.inr (Or.inl (Or.inr (Or.inl head)))
        · exact Or.inr (Or.inl (Or.inr (Or.inr tail)))
        · exact Or.inr (Or.inr suffix)
        · exact Or.inl anchor
        · exact Or.inr (Or.inl (Or.inl before))
    have hab : D.ribbon.black.SameCycle a b := hrot'.sameCycle hnd'
      (List.mem_append_left _ (List.mem_cons_self ..))
      (List.mem_append_right _ (List.mem_cons_self ..))
    have habne : a ≠ b := by
      intro h
      exact (List.nodup_append.mp hnd').2.2 a (List.mem_cons_self ..)
        b (List.mem_cons_self ..) h
    have ha : D.balanced.blackLabel a = none :=
      (D.exposed a).mpr ((hmem a).mpr
        (List.mem_append_left _ (List.mem_cons_self ..)))
    have hb : D.balanced.blackLabel b = none :=
      (D.exposed b).mpr ((hmem b).mpr
        (List.mem_append_right _ (List.mem_cons_self ..)))
    let S := D.ribbon.swapBlack a b
    have hsplit := hrot'.split hnd'
    let E := (D.balanced.split_none a b ha hb hab).fill (a :: r)
      (List.nodup_append.mp hnd').1 hsplit.1 v hinc hsum
    have hmrot : Follows S.black (D.anchor :: (pre ++ post)) := by
      have hh : Follows S.black (post ++ (D.anchor :: pre)) := by
        simpa only [← hbm, S, Ribbon.swapBlack, M] using hsplit.2
      have hn : (post ++ (D.anchor :: pre)).Nodup := by
        simpa only [← hbm] using (List.nodup_append.mp hnd').2.1
      simpa only [List.cons_append] using hh.append_rotate hn
    have hmnd : (D.anchor :: (pre ++ post)).Nodup := by
      have hn : (post ++ (D.anchor :: pre)).Nodup := by
        simpa only [← hbm] using (List.nodup_append.mp hnd').2.1
      simpa only [List.cons_append] using List.nodup_append_comm.mp hn
    have hrem (x : D.Edge) : x ∈ b :: m ↔ x ∈ D.anchor :: (pre ++ post) := by
      simp only [← hbm, M, List.mem_append, List.mem_cons]
      constructor
      · rintro (suffix | anchor | before)
        · exact Or.inr (Or.inr suffix)
        · exact Or.inl anchor
        · exact Or.inr (Or.inl before)
      · rintro (anchor | before | suffix)
        · exact Or.inr (Or.inl anchor)
        · exact Or.inr (Or.inr before)
        · exact Or.inl suffix
    exact ⟨{
      Edge := D.Edge
      fintype := inferInstance
      ribbon := S
      balanced := E
      planar := D.ribbon.genusZero_swapBlack_split D.planar a b habne hab
      anchor := D.anchor
      boundary := pre ++ post
      nodup := hmnd
      rotation := hmrot
      exposed := fun x => by
        change (if x ∈ a :: r then some v else D.balanced.blackLabel x) = none ↔ _
        by_cases hx : x ∈ a :: r
        · rw [ite_eq_left hx]
          constructor
          · exact fun impossible => False.elim (Option.some_ne_none v impossible)
          · intro retained
            exact False.elim
              ((List.nodup_append.mp hnd').2.2 x hx x ((hrem x).mpr retained) rfl)
        · rw [ite_eq_right hx]
          constructor
          · intro exposed
            rcases List.mem_append.mp ((hmem x).mp ((D.exposed x).mp exposed)) with
              removed | retained
            · exact False.elim (hx removed)
            · exact (hrem x).mp retained
          · intro retained
            exact (D.exposed x).mpr ((hmem x).mpr
              (List.mem_append_right _ ((hrem x).mpr retained)))
      anchor_weight := D.anchor_weight
      anchor_label := D.anchor_label
      word := rfl }⟩

end KaplanskyCounterexample.Planar

end

end OAI
