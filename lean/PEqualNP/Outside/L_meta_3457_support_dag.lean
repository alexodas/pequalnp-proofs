import PEqualNP.Outside.L_meta_3457_first_gate
import PEqualNP.Outside.L_meta_3457_union_budget
import PEqualNP.Outside.L_meta_3457_suppress

/-!
The OR shadow has an actual backwards DAG of singleton supports.
A wire with at least two singleton witnesses is an OR gate and
its support is a union of earlier supports. This supplies the
hypothesis of the shared union-budget theorem.
-/

namespace PEqualNP.Outside.L_meta_3457_support_dag

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.MetaComplexity.Helpers.CoverCircB
open PEqualNP.Outside.L_meta_3457_cover_cut
open PEqualNP.Outside.L_meta_3457_shadow
open PEqualNP.Outside.L_meta_3457_first_gate
open PEqualNP.Outside.L_meta_3457_suppress
open PEqualNP.Outside.L_meta_3457_union_budget

local instance : DecidableEq GateOp := gateOpDecEq

def eraseNonOr (g : Gate) : Gate := if g.op = GateOp.or then g else zeroGate

theorem shadow_step_map (w : List Bool) (g : Gate) :
    shadowStep w g = step w (eraseNonOr g) := by
  by_cases h : g.op = GateOp.or
  · simp only [shadowStep, eraseNonOr, h, if_true]
  · simp only [shadowStep, eraseNonOr, h, if_false]
    rfl

theorem shadow_fold_map (gs : List Gate) (w : List Bool) :
    gs.foldl shadowStep w = (gs.map eraseNonOr).foldl step w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, List.foldl_cons, shadow_step_map]
    exact ih _

theorem at_map_shadow (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    atGate (gs.map eraseNonOr) j = eraseNonOr (atGate gs j) := by
  simp [atGate, List.getD_eq_getElem?_getD, hj]

theorem shadow_prefix_eq (gs : List Gate) (w : List Bool) (j i : ℕ)
    (hi : i < w.length + (gs.take j).length) :
    shadowRead gs w i = shadowRead (gs.take j) w i := by
  simp only [shadowRead, shadow_fold_map, List.take_map]
  exact prefix_wire_eq (gs.map eraseNonOr) w j i (by simpa [List.length_take] using hi)

theorem shadow_input_eq (gs : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length) :
    shadowRead gs w i = w.getD i false := by
  simp only [shadowRead, shadow_fold_map]
  exact fold_keep _ _ hi

theorem shadow_beyond_false (gs : List Gate) (w : List Bool) (i : ℕ)
    (hi : w.length + gs.length ≤ i) :
    shadowRead gs w i = false := by
  simp only [shadowRead, shadow_fold_map]
  have hl : ((gs.map eraseNonOr).foldl step w).length = w.length + gs.length := by
    rw [fold_length, List.length_map]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none]

theorem shadow_gate_eval (gs : List Gate) (w : List Bool) (j : ℕ)
    (hj : j < gs.length) :
    shadowRead gs w (w.length+j) =
      if (atGate gs j).op = GateOp.or then
        (atGate gs j).inputs.any (fun i => shadowRead (gs.take j) w i)
      else false := by
  simp only [shadowRead, shadow_fold_map]
  rw [wire_at_gate (gs.map eraseNonOr) w j (by simpa using hj), at_map_shadow gs j hj]
  by_cases ho : (atGate gs j).op = GateOp.or
  · simp [eraseNonOr, ho, GateOp.eval, List.take_map, Function.comp_def]
  · simp [eraseNonOr, ho, zeroGate, GateOp.eval]

def support {n m : ℕ} (C : Circuit) (e : Fin m → Fin n) (i : ℕ) : Finset (Fin m) :=
  Finset.univ.filter (fun k => shadowRead C.gates (singletonRow (e k)) i = true)

theorem mem_support {n m : ℕ} (C : Circuit) (e : Fin m → Fin n) (i : ℕ) (k : Fin m) :
    k ∈ support C e i ↔ shadowRead C.gates (singletonRow (e k)) i = true := by
  simp [support]

theorem support_input_small {n m : ℕ} (C : Circuit) (e : Fin m → Fin n)
    (he : Function.Injective e) (i : ℕ) (hi : i < n) :
    (support C e i).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha b hb
  rw [mem_support] at ha hb
  rw [shadow_input_eq _ _ _ (by simpa [singletonRow] using hi)] at ha hb
  have ha' : (⟨i,hi⟩ : Fin n) = e a := by
    simpa [singletonRow, List.getD_eq_getElem?_getD, hi] using ha
  have hb' : (⟨i,hi⟩ : Fin n) = e b := by
    simpa [singletonRow, List.getD_eq_getElem?_getD, hi] using hb
  exact he (ha'.symm.trans hb')

theorem support_beyond_empty {n m : ℕ} (C : Circuit) (e : Fin m → Fin n)
    (i : ℕ) (hi : n+C.gates.length ≤ i) :
    support C e i = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro k hk
  rw [mem_support, shadow_beyond_false _ _ _ (by simpa [singletonRow] using hi)] at hk
  cases hk

theorem support_nonor_empty {n m : ℕ} (C : Circuit) (e : Fin m → Fin n)
    (j : ℕ) (hj : j < C.gates.length)
    (ho : (atGate C.gates j).op ≠ GateOp.or) :
    support C e (n+j) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro k hk
  rw [mem_support] at hk
  have hw : (singletonRow (e k)).length = n := by simp [singletonRow]
  rw [← hw, shadow_gate_eval C.gates _ j hj, if_neg ho] at hk
  cases hk

theorem support_or_spec {n m : ℕ} (C : Circuit) (e : Fin m → Fin n)
    (hr : ReadsBack n C) (j : ℕ) (hj : j < C.gates.length)
    (ho : (atGate C.gates j).op = GateOp.or) (k : Fin m) :
    k ∈ support C e (n+j) ↔
      ∃ i ∈ (atGate C.gates j).inputs, k ∈ support C e i := by
  rw [mem_support]
  have hw : (singletonRow (e k)).length = n := by simp [singletonRow]
  have he : shadowRead C.gates (singletonRow (e k)) (n+j) =
      (atGate C.gates j).inputs.any (fun i => shadowRead (C.gates.take j) (singletonRow (e k)) i) := by
    rw [← hw, shadow_gate_eval C.gates _ j hj, if_pos ho]
  rw [he, List.any_eq_true]
  have hp : ∀ i ∈ (atGate C.gates j).inputs,
      shadowRead C.gates (singletonRow (e k)) i =
      shadowRead (C.gates.take j) (singletonRow (e k)) i := by
    intro i hi
    apply shadow_prefix_eq
    have h := hr j hj i hi
    simpa [hw, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)] using h
  constructor
  · rintro ⟨i,hi,hv⟩
    exact ⟨i,hi,(mem_support C e i k).mpr ((hp i hi).trans hv)⟩
  · rintro ⟨i,hi,hv⟩
    exact ⟨i,hi,(hp i hi).symm.trans ((mem_support C e i k).mp hv)⟩

/-- Every multi-vertex support can be expanded into two strictly
    earlier supports (a unary OR may use the same operand twice). -/
theorem support_split {n m : ℕ} (C : Circuit) (e : Fin m → Fin n)
    (he : Function.Injective e) (hm : Monotone2 C) (hr : ReadsBack n C)
    (i : ℕ) (hi : 1 < (support C e i).card) :
    ∃ a b, a < i ∧ b < i ∧ support C e i = support C e a ∪ support C e b := by
  have hinput : n ≤ i := by
    by_contra hn
    have hh := support_input_small C e he i (by omega)
    omega
  have hgate : i < n+C.gates.length := by
    by_contra hn
    rw [support_beyond_empty C e i (by omega)] at hi
    simp at hi
  let j := i-n
  have hj : j < C.gates.length := by dsimp [j]; omega
  have hi' : i = n+j := by dsimp [j]; omega
  rw [hi'] at hi ⊢
  have ho : (atGate C.gates j).op = GateOp.or := by
    by_contra hn
    rw [support_nonor_empty C e j hj hn] at hi
    simp at hi
  have hg : atGate C.gates j ∈ C.gates := by
    simp [atGate, List.getD_eq_getElem?_getD, hj]
  have hlen := (hm _ hg).2
  have hspec := support_or_spec C e hr j hj ho
  cases hs : (atGate C.gates j).inputs with
  | nil =>
    have hempty : support C e (n+j) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro k hk
      have hh := (hspec k).mp hk
      simp [hs] at hh
    rw [hempty] at hi
    simp at hi
  | cons a rest =>
    have ha : a < n+j := hr j hj a (by change a ∈ (atGate C.gates j).inputs; simp [hs])
    cases rest with
    | nil =>
      refine ⟨a,a,ha,ha,?_⟩
      ext k
      rw [hspec k]
      simp [hs]
    | cons b rest =>
      have hb : b < n+j := hr j hj b (by change b ∈ (atGate C.gates j).inputs; simp [hs])
      cases rest with
      | nil =>
        refine ⟨a,b,ha,hb,?_⟩
        ext k
        rw [hspec k]
        simp [hs]
      | cons c rest => simp [hs] at hlen


def OrWire (n : ℕ) (C : Circuit) (i : ℕ) : Prop :=
  n ≤ i ∧ i < n+C.gates.length ∧ (atGate C.gates (i-n)).op = GateOp.or

theorem support_large_is_or {n m : ℕ} (C : Circuit) (e : Fin m → Fin n)
    (he : Function.Injective e) (i : ℕ) (hi : 1 < (support C e i).card) :
    OrWire n C i := by
  have hn : n ≤ i := by
    by_contra h
    have hh := support_input_small C e he i (by omega)
    omega
  have hg : i < n+C.gates.length := by
    by_contra h
    rw [support_beyond_empty C e i (by omega)] at hi
    simp at hi
  refine ⟨hn,hg,?_⟩
  by_contra h
  have hidx : i = n+(i-n) := by omega
  have hj : i-n < C.gates.length := by omega
  have hempty := support_nonor_empty C e (i-n) hj h
  have heq : support C e i = ∅ := by
    calc
      support C e i = support C e (n+(i-n)) := congrArg (support C e) hidx
      _ = ∅ := hempty
  rw [heq] at hi
  simp at hi

end PEqualNP.Outside.L_meta_3457_support_dag
