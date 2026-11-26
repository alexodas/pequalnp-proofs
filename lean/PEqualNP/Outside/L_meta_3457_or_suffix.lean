import PEqualNP.Outside.L_meta_3457_cofactor
import PEqualNP.Outside.L_meta_3457_shadow
import PEqualNP.Outside.L_meta_3457_essential_cut

/-!
A terminal dirty AND can be suppressed. If its suffix consists
only of ORs, criticality on an edge makes the slot alone sufficient
to activate the output, independent of the original input.
The argument is stronger than a test on a particular pair.
-/
namespace PEqualNP.Outside.L_meta_3457_or_suffix

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers.CoverCircB
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_3457_cover_cut
open PEqualNP.Outside.L_meta_3457_suppress
open PEqualNP.Outside.L_meta_3457_shadow
open PEqualNP.Outside.L_meta_3457_cofactor
open PEqualNP.Outside.L_meta_3457_essential_cut
open PEqualNP.Outside.L_meta_3457_critical_cut

def OrOnly (gs : List Gate) : Prop :=
  ∀ g ∈ gs, g.op = GateOp.or

theorem or_fold_eq_shadow (gs : List Gate) (w : List Bool)
    (h : OrOnly gs) :
    gs.foldl step w = gs.foldl shadowStep w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    have hg := h g (by simp)
    simp only [List.foldl_cons, shadowStep, hg, if_true]
    exact ih _ (fun g hg => h g (List.mem_cons_of_mem _ hg))

def impulse (m : ℕ) : List Bool := List.replicate m false ++ [true]

theorem impulse_length (m : ℕ) : (impulse m).length = m+1 := by simp [impulse]

theorem impulse_false_prefix (m i : ℕ) (hi : i < m) :
    (impulse m).getD i false = false := by
  rw [impulse, getD_app_left (w := List.replicate m false) (t := [true]) (by simpa using hi)]
  simp [List.getD_eq_getElem?_getD, hi]

theorem impulse_last (m : ℕ) : (impulse m).getD m false = true := by
  unfold impulse
  rw [getD_tail _ _ _ (by simp), List.length_replicate, Nat.sub_self]
  rfl

theorem merge_impulse (w : List Bool) :
    Merge (w ++ [true]) (w ++ [false]) (impulse w.length) := by
  refine ⟨by simp,by simp [impulse],?_⟩
  intro i
  by_cases hi : i < w.length
  · rw [getD_app_left (w := w) (t := [true]) hi,
      getD_app_left (w := w) (t := [false]) hi, impulse_false_prefix _ _ hi]
    cases w.getD i false <;> rfl
  · have hle : w.length ≤ i := by omega
    rw [getD_tail w [true] i hle, getD_tail w [false] i hle]
    unfold impulse
    rw [getD_tail _ _ _ (by simpa using hle), List.length_replicate]
    cases i-w.length <;> rfl

theorem impulse_below (w : List Bool) :
    Below (impulse w.length) (w ++ [true]) := by
  have h := merge_impulse w
  refine ⟨h.2.1.symm,?_⟩
  intro i hi
  rw [h.2.2 i,hi]
  simp

theorem or_suffix_impulse (post : List Gate) (w : List Bool) (o : ℕ)
    (ho : OrOnly post)
    (hl : (post.foldl step (w ++ [false])).getD o false = false)
    (hh : (post.foldl step (w ++ [true])).getD o false = true) :
    (post.foldl step (impulse w.length)).getD o false = true := by
  have hm := shadow_fold_merge post _ _ _ (merge_impulse w)
  rw [← or_fold_eq_shadow post _ ho, ← or_fold_eq_shadow post _ ho,
      ← or_fold_eq_shadow post _ ho] at hm
  have he := hm.2.2 o
  rw [hh,hl] at he
  simpa using he.symm

theorem or_suffix_transfer (post : List Gate) (u v : List Bool) (o : ℕ)
    (ho : OrOnly post) (hlen : u.length = v.length)
    (hl : (post.foldl step (u ++ [false])).getD o false = false)
    (hh : (post.foldl step (u ++ [true])).getD o false = true) :
    (post.foldl step (v ++ [true])).getD o false = true := by
  have h := or_suffix_impulse post u o ho hl hh
  rw [hlen] at h
  have hm : MonoList post := fun g hg => Or.inr (ho g hg)
  exact (fold_below post _ _ (impulse_below v) hm).2 o h

theorem slot_or_suffix_forces (pre post : List Gate) (g : Gate) (o : ℕ)
    (u v : List Bool) (hlen : u.length = v.length)
    (ho : OrOnly post)
    (hu : Sensitive pre post o u) (hv : preValue pre g v = true) :
    (slot pre post g o).eval v = true := by
  rw [slot_eval_mux, hv]
  change high pre post o v = true
  exact or_suffix_transfer post (pre.foldl step u) (pre.foldl step v) o ho
    (by simp only [fold_length,hlen]) hu.1 hu.2

/-- A slot with an OR-only suffix cannot be both active on a
    negative input and critical on any equally long positive input. -/
theorem terminal_dirty_not_critical (pre post : List Gate) (g : Gate) (o : ℕ)
    (u v : List Bool) (hlen : u.length = v.length) (ho : OrOnly post)
    (hpositive : (slot pre post g o).eval u = true)
    (hnegative : (slot pre post g o).eval v = false)
    (hdirty : preValue pre g v = true) :
    (slot pre post zeroGate o).eval u = true := by
  cases hz : (slot pre post zeroGate o).eval u with
  | true => rfl
  | false =>
    have hs := (slot_critical_value pre post g o u hpositive hz).1
    have hv := slot_or_suffix_forces pre post g o u v hlen ho hs hdirty
    rw [hnegative] at hv
    cases hv


theorem gate_split (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    gs.take j ++ atGate gs j :: gs.drop (j+1) = gs := by
  have h : atGate gs j = gs[j] := by
    simp [atGate, List.getD_eq_getElem?_getD, hj]
  rw [h, ← List.drop_eq_getElem_cons hj, List.take_append_drop]

theorem gate_set_split (gs : List Gate) (j : ℕ) (g : Gate)
    (hj : j < gs.length) :
    gs.set j g = gs.take j ++ g :: gs.drop (j+1) := by
  induction gs generalizing j with
  | nil => simp at hj
  | cons k ks ih =>
    cases j with
    | zero => rfl
    | succ j =>
      have hh : j < ks.length := by simp at hj; omega
      simp only [List.set_cons_succ, List.take_succ_cons, List.cons_append,
        Nat.succ_add, List.drop_succ_cons]
      exact congrArg (List.cons k) (ih j hh)

theorem circuit_as_slot (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    slot (C.gates.take j) (C.gates.drop (j+1)) (atGate C.gates j) C.output = C := by
  cases C with
  | mk gs o =>
    unfold slot
    rw [gate_split gs j hj]

theorem suppression_as_slot (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    suppress C j = slot (C.gates.take j) (C.gates.drop (j+1)) zeroGate C.output := by
  unfold suppress slot
  rw [gate_set_split C.gates j zeroGate hj]

/-- The original circuit's terminal dirty gate is never critical. -/
theorem terminal_dirty_not_critical_circuit (N : ℕ) (I : Fin N → Fin N → Prop)
    (C : Circuit) (h : Admissible N I C) (j : ℕ) (p l : Fin N)
    (hd : (j,p,l) ∈ dirtySites N I C)
    (ho : OrOnly (C.gates.drop (j+1))) :
    ¬ Critical N I C j := by
  obtain ⟨hj,hn,hop,hv⟩ := (mem_dirtySites N I C j p l).mp hd
  intro hc
  obtain ⟨q,m,hi,hzero⟩ := hc
  let v := doubleRow (Fin.castAdd N p) (Fin.natAdd N l)
  let u := doubleRow (Fin.castAdd N q) (Fin.natAdd N m)
  have hvlen : v.length = N+N := by simp [v,doubleRow]
  have hulen : u.length = N+N := by simp [u,doubleRow]
  have hnegative : C.eval v = false := by
    cases he : C.eval v with
    | false => rfl
    | true =>
      obtain ⟨p',l',hi',hp,hl⟩ := (h.2.2.1
        (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l))).mp he
      have hp' := of_decide_eq_true hp
      have hl' := of_decide_eq_true hl
      have hp'' := hp'.resolve_right (point_line_distinct N p' l)
      have hl'' := hl'.resolve_left (Ne.symm (point_line_distinct N p l'))
      have ep : p' = p := by
        apply Fin.ext
        exact congrArg (fun k : Fin (N+N) => k.val) hp''
      have el : l' = l := by
        apply Fin.ext
        have hh := congrArg (fun k : Fin (N+N) => k.val) hl''
        simp only [Fin.val_natAdd] at hh
        omega
      exact False.elim (hn (ep ▸ el ▸ hi'))
  have hpositive : C.eval u = true := by
    apply (h.2.2.1 (fun k => decide (k = Fin.castAdd N q ∨ k = Fin.natAdd N m))).mpr
    exact ⟨q,m,hi,by simp,by simp⟩
  have hdirty : preValue (C.gates.take j) (atGate C.gates j) v = true := by
    change (C.gates.foldl step v).getD (N+N+j) false = true at hv
    rw [← hvlen, PEqualNP.Outside.L_meta_3457_first_gate.wire_at_gate C.gates v j hj] at hv
    exact hv
  have he := circuit_as_slot C j hj
  have hz := terminal_dirty_not_critical (C.gates.take j) (C.gates.drop (j+1))
    (atGate C.gates j) C.output u v (hulen.trans hvlen.symm) ho
    (by simpa only [he] using hpositive) (by simpa only [he] using hnegative) hdirty
  rw [← suppression_as_slot C j hj] at hz
  change (suppress C j).eval u = false at hzero
  rw [hzero] at hz
  cases hz

theorem critical_dirty_requires_nonor_suffix (N : ℕ) (I : Fin N → Fin N → Prop)
    (C : Circuit) (h : Admissible N I C) (j : ℕ) (p l : Fin N)
    (hd : (j,p,l) ∈ dirtySites N I C) (hc : Critical N I C j) :
    ¬ OrOnly (C.gates.drop (j+1)) :=
  fun ho => terminal_dirty_not_critical_circuit N I C h j p l hd ho hc

end PEqualNP.Outside.L_meta_3457_or_suffix
