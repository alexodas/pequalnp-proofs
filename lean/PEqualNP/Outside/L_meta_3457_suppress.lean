import PEqualNP.Outside.L_meta_3457_first_gate

/-!
A fixed-position suppression pays no wire-renumbering cost.
It preserves the structural conditions and can only turn wires off.
This is the easy case of the coordinator's suggested counting cut.
-/

namespace PEqualNP.Outside.L_meta_3457_suppress

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.MetaComplexity.Helpers.CoverCircB
open PEqualNP.Outside.L_meta_3457_cover_cut
open PEqualNP.Outside.L_meta_3457_shadow
open PEqualNP.Outside.L_meta_3457_first_gate

def Below (u v : List Bool) : Prop :=
  u.length = v.length ∧ ∀ i : ℕ, u.getD i false = true → v.getD i false = true

theorem below_refl (w : List Bool) : Below w w := ⟨rfl, fun _ h => h⟩

theorem below_snoc (u v : List Bool) (a b : Bool) (h : Below u v)
    (hab : a = true → b = true) : Below (u ++ [a]) (v ++ [b]) := by
  obtain ⟨hlen,h⟩ := h
  refine ⟨by simp [hlen], ?_⟩
  intro i hi
  by_cases hlt : i < u.length
  · rw [getD_app_left (w := u) (t := [a]) hlt] at hi
    rw [getD_app_left (w := v) (t := [b]) (by omega)]
    exact h i hi
  · have hle : u.length ≤ i := by omega
    have hle' : v.length ≤ i := by omega
    rw [getD_tail u [a] i hle] at hi
    rw [getD_tail v [b] i hle', ← hlen]
    cases hk : i-u.length with
    | zero =>
      have ha : a = true := by simpa [hk] using hi
      simpa using hab ha
    | succ k => simp [hk] at hi

theorem eval_mono (g : Gate) (u v : List Bool) (h : Below u v)
    (hg : g.op = GateOp.and ∨ g.op = GateOp.or) :
    g.op.eval (g.inputs.map fun i => u.getD i false) = true →
      g.op.eval (g.inputs.map fun i => v.getD i false) = true := by
  rcases hg with hg | hg
  · simp only [hg, GateOp.eval, List.all_map, Function.comp_def, List.all_eq_true, id]
    intro hu i hi
    exact h.2 i (hu i hi)
  · simp only [hg, GateOp.eval, List.any_map, Function.comp_def, List.any_eq_true, id]
    rintro ⟨i,hi,hu⟩
    exact ⟨i,hi,h.2 i hu⟩

theorem step_below (g : Gate) (u v : List Bool) (h : Below u v)
    (hg : g.op = GateOp.and ∨ g.op = GateOp.or) :
    Below (step u g) (step v g) :=
  below_snoc _ _ _ _ h (eval_mono g u v h hg)

def MonoList (gs : List Gate) : Prop :=
  ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or

theorem fold_below (gs : List Gate) (u v : List Bool)
    (h : Below u v) (hm : MonoList gs) :
    Below (gs.foldl step u) (gs.foldl step v) := by
  induction gs generalizing u v with
  | nil => exact h
  | cons g gs ih =>
    simp only [List.foldl_cons]
    exact ih _ _ (step_below g u v h (hm g (by simp)))
      (fun g hg => hm g (List.mem_cons_of_mem _ hg))

def zeroGate : Gate := ⟨GateOp.or, []⟩
def suppress (C : Circuit) (j : ℕ) : Circuit := ⟨C.gates.set j zeroGate, C.output⟩

theorem suppress_fold_below (gs : List Gate) (j : ℕ) (w : List Bool)
    (hm : MonoList gs) :
    Below ((gs.set j zeroGate).foldl step w) (gs.foldl step w) := by
  induction gs generalizing j w with
  | nil => exact below_refl w
  | cons g gs ih =>
    have hm' : MonoList gs := fun k hk => hm k (List.mem_cons_of_mem _ hk)
    cases j with
    | zero =>
      simp only [List.set_cons_zero, List.foldl_cons]
      apply fold_below gs _ _ _ hm'
      change Below (w ++ [false]) (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      exact below_snoc _ _ _ _ (below_refl w) (by simp)
    | succ j =>
      simp only [List.set_cons_succ, List.foldl_cons]
      exact ih j (step w g) hm'

theorem suppress_size (C : Circuit) (j : ℕ) :
    (suppress C j).size = C.size := by simp [suppress, Circuit.size]

theorem suppress_monotone (C : Circuit) (j : ℕ) (hm : Monotone2 C) :
    Monotone2 (suppress C j) := by
  intro g hg
  change g ∈ C.gates.set j zeroGate at hg
  rcases List.mem_or_eq_of_mem_set hg with h | rfl
  · exact hm g h
  · simp [zeroGate]

theorem suppress_at_self (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt (suppress C j) j = zeroGate := by
  simp only [gateAt, suppress, List.getD_eq_getElem?_getD, List.getElem?_set_self hj,
    Option.getD_some]

theorem suppress_at_other (C : Circuit) (j k : ℕ) (h : j ≠ k) :
    gateAt (suppress C j) k = gateAt C k := by
  simp only [gateAt, suppress, List.getD_eq_getElem?_getD, List.getElem?_set_ne h]

theorem suppress_reads_back (n : ℕ) (C : Circuit) (j : ℕ)
    (h : ReadsBack n C) : ReadsBack n (suppress C j) := by
  intro k hk i hi
  have hk' : k < C.gates.length := by simpa [suppress] using hk
  by_cases he : j = k
  · subst k
    rw [suppress_at_self C j hk'] at hi
    simp [zeroGate] at hi
  · rw [suppress_at_other C j k he] at hi
    exact h k hk' i hi

theorem suppress_wires_below (C : Circuit) (j : ℕ) (hm : Monotone2 C)
    (w : List Bool) : Below ((suppress C j).wires w) (C.wires w) := by
  simp only [wires_eq, suppress]
  apply suppress_fold_below
  intro g hg
  simpa using (hm g hg).1

theorem suppress_eval_below (C : Circuit) (j : ℕ) (hm : Monotone2 C)
    (w : List Bool) :
    (suppress C j).eval w = true → C.eval w = true :=
  (suppress_wires_below C j hm w).2 C.output

theorem suppress_and_off (C : Circuit) (j k : ℕ) (hm : Monotone2 C)
    (hk : k < (suppress C j).gates.length)
    (hop : (gateAt (suppress C j) k).op = GateOp.and)
    (w : List Bool) (h : (C.wires w).getD (w.length+k) false = false) :
    ((suppress C j).wires w).getD (w.length+k) false = false := by
  cases he : ((suppress C j).wires w).getD (w.length+k) false with
  | false => rfl
  | true =>
    have hh := (suppress_wires_below C j hm w).2 (w.length+k) he
    rw [h] at hh
    cases hh

/-- Every true AND after suppression was already a true AND before
    suppression, and is at a different position from the suppressed gate. -/
theorem suppress_active_subset (C : Circuit) (j k : ℕ) (hm : Monotone2 C)
    (hk : k < (suppress C j).gates.length)
    (hop : (gateAt (suppress C j) k).op = GateOp.and)
    (w : List Bool) (hv : ((suppress C j).wires w).getD (w.length+k) false = true) :
    k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧
      (C.wires w).getD (w.length+k) false = true ∧ j ≠ k := by
  have hk' : k < C.gates.length := by simpa [suppress] using hk
  have hne : j ≠ k := by
    intro he
    subst k
    rw [suppress_at_self C j hk'] at hop
    cases hop
  exact ⟨hk', (suppress_at_other C j k hne) ▸ hop,
    (suppress_wires_below C j hm w).2 _ hv, hne⟩

end PEqualNP.Outside.L_meta_3457_suppress
