import Mathlib
import PEqualNP.Defs

/-!
An explicit obstruction to fixed-prefix, fixed-suffix local repair.
The C4-free three-edge path has a five-gate dirty implementation.
No one-gate replacement at the dirty slot cleans it while keeping
the function and respecting fan-in two and backward reads.
A four-gate clean implementation nevertheless exists.
-/

namespace PEqualNP.Outside.L_meta_3457_local_barrier

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover

local instance : DecidableEq GateOp := gateOpDecEq

def target (a b c d : Bool) : Bool :=
  (a && c) || (a && d) || (b && c)

def slot (g : Gate) : Circuit :=
  ⟨[⟨GateOp.or,[0,1]⟩, ⟨GateOp.or,[2,3]⟩, g,
     ⟨GateOp.or,[0,2]⟩, ⟨GateOp.and,[6,7]⟩],8⟩

def original : Circuit := slot ⟨GateOp.and,[4,5]⟩
def clean : Circuit :=
  ⟨[⟨GateOp.or,[2,3]⟩, ⟨GateOp.and,[0,4]⟩,
     ⟨GateOp.and,[1,2]⟩, ⟨GateOp.or,[5,6]⟩],7⟩

def Correct (C : Circuit) : Prop :=
  ∀ a b c d : Bool, C.eval [a,b,c,d] = target a b c d

instance (C : Circuit) : Decidable (Correct C) := by
  unfold Correct
  infer_instance

def SlotOK (g : Gate) : Prop :=
  Correct (slot g) ∧
    (g.op = GateOp.and → ((slot g).wires [false,true,false,true]).getD 6 false = false)

instance (g : Gate) : Decidable (SlotOK g) := by
  unfold SlotOK
  infer_instance

theorem original_correct : Correct original := by decide
theorem clean_correct : Correct clean := by decide
theorem clean_smaller : clean.size < original.size := by decide
theorem original_reads_back : ReadsBack 4 original := by decide
theorem clean_reads_back : ReadsBack 4 clean := by decide

theorem original_dirty :
    (original.wires [false,true,false,true]).getD 6 false = true := by decide

theorem original_singleton_safe :
    ∀ j : Fin 5, (gateAt original j.val).op = GateOp.and →
      ∀ k : Fin 4,
        (original.wires (List.ofFn (fun i : Fin 4 => decide (i=k)))).getD
          (4+j.val) false = false := by decide

theorem clean_ands_below_output :
    ∀ j : Fin 4, (gateAt clean j.val).op = GateOp.and →
      ∀ a b c d : Bool,
        (clean.wires [a,b,c,d]).getD (4+j.val) false = true →
        clean.eval [a,b,c,d] = true := by decide

theorem no_and_zero : ¬ SlotOK ⟨GateOp.and,[]⟩ := by decide
theorem no_or_zero : ¬ SlotOK ⟨GateOp.or,[]⟩ := by decide
theorem no_and_one : ∀ a : Fin 6, ¬ SlotOK ⟨GateOp.and,[a.val]⟩ := by decide
theorem no_or_one : ∀ a : Fin 6, ¬ SlotOK ⟨GateOp.or,[a.val]⟩ := by decide
theorem no_and_two : ∀ a b : Fin 6, ¬ SlotOK ⟨GateOp.and,[a.val,b.val]⟩ := by decide
theorem no_or_two : ∀ a b : Fin 6, ¬ SlotOK ⟨GateOp.or,[a.val,b.val]⟩ := by decide

/-- Any allowed single-gate repair of this slot is impossible. -/
theorem no_local_repair (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hlen : g.inputs.length ≤ 2)
    (hback : ∀ i ∈ g.inputs, i < 6) : ¬ SlotOK g := by
  rcases g with ⟨op, ins⟩
  change op = GateOp.and ∨ op = GateOp.or at hop
  change ins.length ≤ 2 at hlen
  change ∀ i ∈ ins, i < 6 at hback
  cases ins with
  | nil =>
    rcases hop with rfl | rfl
    · exact no_and_zero
    · exact no_or_zero
  | cons a rest =>
    have ha : a < 6 := hback a (by simp)
    cases rest with
    | nil =>
      rcases hop with rfl | rfl
      · exact no_and_one ⟨a,ha⟩
      · exact no_or_one ⟨a,ha⟩
    | cons b rest =>
      have hb : b < 6 := hback b (by simp)
      cases rest with
      | nil =>
        rcases hop with rfl | rfl
        · exact no_and_two ⟨a,ha⟩ ⟨b,hb⟩
        · exact no_or_two ⟨a,ha⟩ ⟨b,hb⟩
      | cons c rest => simp at hlen

/-- Suppressing the dirty slot loses every one of the three edges. -/
theorem all_three_critical :
    (slot ⟨GateOp.or,[]⟩).eval [true,false,true,false] = false ∧
    (slot ⟨GateOp.or,[]⟩).eval [true,false,false,true] = false ∧
    (slot ⟨GateOp.or,[]⟩).eval [false,true,true,false] = false := by decide

end PEqualNP.Outside.L_meta_3457_local_barrier
