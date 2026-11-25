import PEqualNP.Outside.L_meta_3457_suppress

/-!
A fixed-slot cofactor criterion for repair. The suffix is viewed
as a monotone function of the value produced at the selected slot.
On a sensitive row the replacement must agree with the original
slot value; on all other rows it may do either.
-/

namespace PEqualNP.Outside.L_meta_3457_cofactor

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers.CoverCircB
open PEqualNP.Outside.L_meta_3457_suppress

def slot (pre post : List Gate) (g : Gate) (o : ℕ) : Circuit :=
  ⟨pre ++ g :: post, o⟩

def preValue (pre : List Gate) (g : Gate) (w : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => (pre.foldl step w).getD i false)

def suffixValue (pre post : List Gate) (o : ℕ) (w : List Bool) (b : Bool) : Bool :=
  (post.foldl step ((pre.foldl step w) ++ [b])).getD o false

def low (pre post : List Gate) (o : ℕ) (w : List Bool) : Bool :=
  suffixValue pre post o w false

def high (pre post : List Gate) (o : ℕ) (w : List Bool) : Bool :=
  suffixValue pre post o w true

def Sensitive (pre post : List Gate) (o : ℕ) (w : List Bool) : Prop :=
  low pre post o w = false ∧ high pre post o w = true

theorem slot_eval (pre post : List Gate) (g : Gate) (o : ℕ) (w : List Bool) :
    (slot pre post g o).eval w =
      suffixValue pre post o w (preValue pre g w) := by
  simp only [slot, Circuit.eval, wires_eq, List.foldl_append, List.foldl_cons,
    suffixValue, preValue, step]

theorem low_le_high (pre post : List Gate) (o : ℕ) (w : List Bool)
    (hm : MonoList post) :
    low pre post o w = true → high pre post o w = true := by
  apply (fold_below post _ _ _ hm).2 o
  exact below_snoc _ _ false true (below_refl _) (by simp)

theorem bool_cofactor (lo hi a b : Bool)
    (hm : lo = true → hi = true) :
    (if a then hi else lo) = (if b then hi else lo) ↔
      ((lo = false ∧ hi = true) → a = b) := by
  cases lo <;> cases hi <;> cases a <;> cases b <;> simp_all

theorem slot_eval_mux (pre post : List Gate) (g : Gate) (o : ℕ) (w : List Bool) :
    (slot pre post g o).eval w =
      if preValue pre g w then high pre post o w else low pre post o w := by
  rw [slot_eval]
  cases h : preValue pre g w <;> rfl

theorem slot_agreement_iff (pre post : List Gate) (g r : Gate)
    (o : ℕ) (w : List Bool) (hm : MonoList post) :
    (slot pre post g o).eval w = (slot pre post r o).eval w ↔
      (Sensitive pre post o w → preValue pre g w = preValue pre r w) := by
  rw [slot_eval_mux, slot_eval_mux]
  exact bool_cofactor _ _ _ _ (low_le_high pre post o w hm)

theorem slot_agreement_all (pre post : List Gate) (g r : Gate)
    (o : ℕ) (n : ℕ) (hm : MonoList post) :
    (∀ x : Fin n → Bool, (slot pre post g o).eval (List.ofFn x) =
      (slot pre post r o).eval (List.ofFn x)) ↔
      (∀ x : Fin n → Bool, Sensitive pre post o (List.ofFn x) →
        preValue pre g (List.ofFn x) = preValue pre r (List.ofFn x)) := by
  constructor <;> intro h x
  · exact (slot_agreement_iff pre post g r o _ hm).mp (h x)
  · exact (slot_agreement_iff pre post g r o _ hm).mpr (h x)

theorem slot_zero_eval (pre post : List Gate) (o : ℕ) (w : List Bool) :
    (slot pre post zeroGate o).eval w = low pre post o w := by
  rw [slot_eval]
  rfl

theorem slot_critical_value (pre post : List Gate) (g : Gate)
    (o : ℕ) (w : List Bool)
    (hpos : (slot pre post g o).eval w = true)
    (hneg : (slot pre post zeroGate o).eval w = false) :
    Sensitive pre post o w ∧ preValue pre g w = true := by
  rw [slot_zero_eval] at hneg
  rw [slot_eval_mux] at hpos
  cases hv : preValue pre g w with
  | false => simp [hv, hneg] at hpos
  | true =>
    have hh : high pre post o w = true := by simpa [hv] using hpos
    exact ⟨⟨hneg,hh⟩,rfl⟩

theorem slot_preserves_positive_iff (pre post : List Gate) (g r : Gate)
    (o : ℕ) (w : List Bool) (hm : MonoList post)
    (hpos : (slot pre post g o).eval w = true) :
    (slot pre post r o).eval w = true ↔
      (low pre post o w = false → preValue pre r w = true) := by
  have hh : high pre post o w = true := by
    rw [slot_eval_mux] at hpos
    cases hv : preValue pre g w with
    | false => exact low_le_high pre post o w hm (by simpa [hv] using hpos)
    | true => simpa [hv] using hpos
  rw [slot_eval_mux, hh]
  cases hl : low pre post o w <;> cases hv : preValue pre r w <;> simp_all

theorem slot_preserves_negative_iff (pre post : List Gate) (g r : Gate)
    (o : ℕ) (w : List Bool) (hm : MonoList post)
    (hneg : (slot pre post g o).eval w = false) :
    (slot pre post r o).eval w = false ↔
      (high pre post o w = true → preValue pre r w = false) := by
  have hl : low pre post o w = false := by
    rw [slot_eval_mux] at hneg
    cases hv : preValue pre g w with
    | false => simpa [hv] using hneg
    | true =>
      have hh : high pre post o w = false := by simpa [hv] using hneg
      cases hl : low pre post o w with
      | false => rfl
      | true =>
        have ht := low_le_high pre post o w hm hl
        rw [hh] at ht
        cases ht
  rw [slot_eval_mux, hl]
  cases hh : high pre post o w <;> cases hv : preValue pre r w <;> simp_all

end PEqualNP.Outside.L_meta_3457_cofactor
