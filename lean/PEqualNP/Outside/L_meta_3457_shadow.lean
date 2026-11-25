import PEqualNP.Outside.L_meta_3457_cover_cut
import PEqualNP.Outside.L_meta_3457_rectangles

/-!
The OR shadow of a prefix replaces each non-OR by false.
It preserves coordinatewise unions, and agrees with the actual
prefix on any row on which all non-OR gates are inactive.
-/

namespace PEqualNP.Outside.L_meta_3457_shadow

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.Helpers.CoverCircB
open PEqualNP.Outside.L_meta_3457_cover_cut
open PEqualNP.MetaComplexity.NestedCover

local instance : DecidableEq GateOp := gateOpDecEq

def Merge (w u v : List Bool) : Prop :=
  w.length = u.length ∧ w.length = v.length ∧
    ∀ i : ℕ, w.getD i false = (u.getD i false || v.getD i false)

def shadowStep (w : List Bool) (g : Gate) : List Bool :=
  if g.op = GateOp.or then step w g else w ++ [false]

theorem getD_tail (w t : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    (w ++ t).getD i false = t.getD (i - w.length) false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right hi,
    ← List.getD_eq_getElem?_getD]

theorem merge_snoc (w u v : List Bool) (a b c : Bool) (h : Merge w u v)
    (he : a = (b || c)) : Merge (w ++ [a]) (u ++ [b]) (v ++ [c]) := by
  obtain ⟨hu, hv, hm⟩ := h
  refine ⟨by simp [hu], by simp [hv], ?_⟩
  intro i
  by_cases hi : i < w.length
  · rw [getD_app_left (w := w) (t := [a]) hi,
      getD_app_left (w := u) (t := [b]) (by omega : i < u.length),
      getD_app_left (w := v) (t := [c]) (by omega : i < v.length), hm]
  · rw [getD_tail w [a] i (by omega), getD_tail u [b] i (by omega),
      getD_tail v [c] i (by omega), ← hu, ← hv]
    cases hidx : i - w.length with
    | zero => simpa using he
    | succ k => simp

theorem any_merge (ins : List ℕ) (w u v : List Bool) (h : Merge w u v) :
    ins.any (fun i => w.getD i false) =
      (ins.any (fun i => u.getD i false) || ins.any (fun i => v.getD i false)) := by
  induction ins with
  | nil => rfl
  | cons i ins ih =>
    simp only [List.any_cons]
    rw [h.2.2 i, ih]
    cases u.getD i false <;> cases v.getD i false <;>
      cases ins.any (fun i => u.getD i false) <;>
      cases ins.any (fun i => v.getD i false) <;> rfl

theorem shadow_step_merge (w u v : List Bool) (g : Gate) (h : Merge w u v) :
    Merge (shadowStep w g) (shadowStep u g) (shadowStep v g) := by
  by_cases hg : g.op = GateOp.or
  · simp only [shadowStep, hg, if_true, step, GateOp.eval, List.any_map, Function.comp_def]
    apply merge_snoc _ _ _ _ _ _ h
    simpa using any_merge g.inputs w u v h
  · simp only [shadowStep, hg, if_false]
    exact merge_snoc w u v false false false h rfl

theorem shadow_fold_merge (gs : List Gate) (w u v : List Bool) (h : Merge w u v) :
    Merge (gs.foldl shadowStep w) (gs.foldl shadowStep u) (gs.foldl shadowStep v) := by
  induction gs generalizing w u v with
  | nil => exact h
  | cons g gs ih =>
    simp only [List.foldl_cons]
    exact ih _ _ _ (shadow_step_merge w u v g h)

def Silent (gs : List Gate) (w : List Bool) : Prop :=
  ∀ j < gs.length, (atGate gs j).op ≠ GateOp.or →
    (gs.foldl step w).getD (w.length + j) false = false

theorem step_length (w : List Bool) (g : Gate) :
    (step w g).length = w.length + 1 := by simp [step]

theorem shadow_fold_eq (gs : List Gate) (w : List Bool) (h : Silent gs w) :
    gs.foldl shadowStep w = gs.foldl step w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    have hstep : shadowStep w g = step w g := by
      by_cases hg : g.op = GateOp.or
      · simp [shadowStep, hg]
      · have hz := h 0 (by simp) (by simpa [atGate] using hg)
        simp only [List.foldl_cons, Nat.add_zero] at hz
        rw [fold_keep gs (step w g) (by rw [step_length]; omega)] at hz
        have hval : g.op.eval (g.inputs.map fun i => w.getD i false) = false := by
          unfold step at hz
          rw [getD_snoc' w _ _ rfl] at hz
          exact hz
        simp [shadowStep, hg, step, hval]
    have ht : Silent gs (step w g) := by
      intro j hj hop
      have hp : (atGate (g :: gs) (j+1)).op ≠ GateOp.or := by
        simpa only [atGate, List.getD_cons_succ] using hop
      have hz := h (j+1) (by simp; omega) hp
      rw [List.foldl_cons] at hz
      rw [step_length]
      simpa only [Nat.add_assoc, Nat.add_comm 1 j] using hz
    simp only [List.foldl_cons, hstep]
    exact ih _ ht

/-- The two operands of the first active AND see the union of their
    singleton values, provided the prefix is silent on these rows. -/
theorem first_binary_and_trace (gs : List Gate) (w u v : List Bool)
    (a b : ℕ) (hm : Merge w u v)
    (hw : Silent gs w) (hu : Silent gs u) (hv : Silent gs v) :
    ((gs.foldl step w).getD a false && (gs.foldl step w).getD b false) =
      (((gs.foldl step u).getD a false || (gs.foldl step v).getD a false) &&
        ((gs.foldl step u).getD b false || (gs.foldl step v).getD b false)) := by
  have h := shadow_fold_merge gs w u v hm
  rw [shadow_fold_eq gs w hw, shadow_fold_eq gs u hu, shadow_fold_eq gs v hv] at h
  rw [h.2.2 a, h.2.2 b]


def singletonRow {n : ℕ} (i : Fin n) : List Bool :=
  List.ofFn (fun k : Fin n => decide (k = i))

def doubleRow {n : ℕ} (i j : Fin n) : List Bool :=
  List.ofFn (fun k : Fin n => decide (k = i ∨ k = j))

theorem merge_double_row {n : ℕ} (i j : Fin n) :
    Merge (doubleRow i j) (singletonRow i) (singletonRow j) := by
  refine ⟨by simp [doubleRow, singletonRow], by simp [doubleRow, singletonRow], ?_⟩
  intro k
  by_cases hk : k < n
  · simp [doubleRow, singletonRow, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hk]
  · simp [doubleRow, singletonRow, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hk]

/-- Every positive pair with negative singleton outputs must activate
    at least one non-OR gate, if the singleton rows are silent. -/
theorem exists_active_nonor (gs : List Gate) (w u v : List Bool) (o : ℕ)
    (hm : Merge w u v) (hu : Silent gs u) (hv : Silent gs v)
    (hU : (gs.foldl step u).getD o false = false)
    (hV : (gs.foldl step v).getD o false = false)
    (hW : (gs.foldl step w).getD o false = true) :
    ∃ j < gs.length, (atGate gs j).op ≠ GateOp.or ∧
      (gs.foldl step w).getD (w.length + j) false = true := by
  classical
  by_contra h
  have hw : Silent gs w := by
    intro j hj hop
    cases he : (gs.foldl step w).getD (w.length+j) false with
    | false => rfl
    | true => exact False.elim (h ⟨j, hj, hop, he⟩)
  have hm' := shadow_fold_merge gs w u v hm
  rw [shadow_fold_eq gs w hw, shadow_fold_eq gs u hu, shadow_fold_eq gs v hv] at hm'
  have he := hm'.2.2 o
  rw [hW, hU, hV] at he
  cases he

/-- Choose the earliest active non-OR gate and obtain a silent past. -/
theorem earliest_active_nonor (gs : List Gate) (w : List Bool)
    (h : ∃ j < gs.length, (atGate gs j).op ≠ GateOp.or ∧
      (gs.foldl step w).getD (w.length + j) false = true) :
    ∃ j < gs.length, (atGate gs j).op ≠ GateOp.or ∧
      (gs.foldl step w).getD (w.length + j) false = true ∧
      ∀ i < j, (atGate gs i).op ≠ GateOp.or →
        (gs.foldl step w).getD (w.length + i) false = false := by
  classical
  obtain ⟨hj, hop, hval⟩ := Nat.find_spec h
  refine ⟨Nat.find h, hj, hop, hval, ?_⟩
  intro i hi hio
  cases he : (gs.foldl step w).getD (w.length+i) false with
  | false => rfl
  | true =>
    have hh : i < gs.length ∧ (atGate gs i).op ≠ GateOp.or ∧
        (gs.foldl step w).getD (w.length + i) false = true :=
      ⟨lt_trans hi hj, hio, he⟩
    have hle := Nat.find_min' h hh
    omega

theorem monotone_gate_nonor_is_and (C : Circuit)
    (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (j : ℕ) (hj : j < C.gates.length)
    (hn : (atGate C.gates j).op ≠ GateOp.or) :
    (atGate C.gates j).op = GateOp.and := by
  have hg : atGate C.gates j ∈ C.gates := by
    simp [atGate, List.getD_eq_getElem?_getD, hj]
  have hop : (atGate C.gates j).op = GateOp.and ∨
      (atGate C.gates j).op = GateOp.or := by
    simpa using (hm _ hg).1
  exact hop.resolve_right hn

end PEqualNP.Outside.L_meta_3457_shadow
