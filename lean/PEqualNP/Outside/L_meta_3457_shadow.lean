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
  · rw [getD_app_left hi, getD_app_left (by omega : i < u.length),
      getD_app_left (by omega : i < v.length), hm]
  · rw [getD_tail _ _ _ (by omega), getD_tail _ _ _ (by omega),
      getD_tail _ _ _ (by omega), ← hu, ← hv]
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

end PEqualNP.Outside.L_meta_3457_shadow
