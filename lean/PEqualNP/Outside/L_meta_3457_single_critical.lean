import PEqualNP.Outside.L_meta_3457_replace

/-!
A genuine progress theorem for the case of a unique critical
incidence pair. Replace the dirty AND by the AND of that edge's
two input variables. The replacement stays below the old gate
on every row, preserves all positive pairs, and is mixed-clean.
-/
namespace PEqualNP.Outside.L_meta_3457_single_critical

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.MetaComplexity.Helpers.CoverCircB
open PEqualNP.Outside.L_meta_3457_cover_cut
open PEqualNP.Outside.L_meta_3457_shadow
open PEqualNP.Outside.L_meta_3457_suppress
open PEqualNP.Outside.L_meta_3457_critical_cut
open PEqualNP.Outside.L_meta_3457_essential_cut
open PEqualNP.Outside.L_meta_3457_cofactor
open PEqualNP.Outside.L_meta_3457_or_suffix
open PEqualNP.Outside.L_meta_3457_replace

def inputAnd {n : ℕ} (a b : Fin n) : Gate :=
  ⟨GateOp.and,[a.val,b.val]⟩

theorem input_and_value {n : ℕ} (pre : List Gate) (a b : Fin n)
    (w : List Bool) (hw : w.length = n) :
    preValue pre (inputAnd a b) w =
      (w.getD a.val false && w.getD b.val false) := by
  have ha : a.val < w.length := by rw [hw]; exact a.isLt
  have hb : b.val < w.length := by rw [hw]; exact b.isLt
  simp only [preValue,inputAnd,GateOp.eval,List.map_cons,List.map_nil,
    List.all_cons,List.all_nil,id,Bool.and_true]
  rw [fold_keep pre w ha,fold_keep pre w hb]

theorem pair_below_list {n : ℕ} (a b : Fin n) (w : List Bool)
    (hw : w.length = n) (ha : w.getD a.val false = true)
    (hb : w.getD b.val false = true) :
    Below (doubleRow a b) w := by
  refine ⟨by simp [doubleRow,hw],?_⟩
  intro i hi
  by_cases h : i < n
  · have hh : (⟨i,h⟩ : Fin n) = a ∨ (⟨i,h⟩ : Fin n) = b := by
      simpa [doubleRow,List.getD_eq_getElem?_getD,h] using hi
    rcases hh with hh | hh
    · have he : i = a.val := congrArg Fin.val hh
      rw [he]
      exact ha
    · have he : i = b.val := congrArg Fin.val hh
      rw [he]
      exact hb
  · simp [doubleRow,List.getD_eq_getElem?_getD,h] at hi

theorem original_slot_mono (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (hm : Monotone2 C) (u v : List Bool) (h : Below u v) :
    preValue (C.gates.take j) (atGate C.gates j) u = true →
      preValue (C.gates.take j) (atGate C.gates j) v = true := by
  have hpre : MonoList (C.gates.take j) := by
    intro g hg
    simpa using (hm g (List.mem_of_mem_take hg)).1
  have hg : atGate C.gates j ∈ C.gates := by
    simp [atGate,List.getD_eq_getElem?_getD,hj]
  exact eval_mono _ _ _ (fold_below _ _ _ h hpre) (by simpa using (hm _ hg).1)

theorem critical_pair_slot_true (N : ℕ) (I : Fin N → Fin N → Prop)
    (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (h : Admissible N I C) (p l : Fin N) (hc : CriticalPair N I C j p l) :
    preValue (C.gates.take j) (atGate C.gates j)
      (doubleRow (Fin.castAdd N p) (Fin.natAdd N l)) = true := by
  let w := doubleRow (Fin.castAdd N p) (Fin.natAdd N l)
  have hp : C.eval w = true := by
    apply (h.2.2.1 (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l))).mpr
    exact ⟨p,l,hc.1,by simp,by simp⟩
  have hs : (slot (C.gates.take j) (C.gates.drop (j+1)) zeroGate C.output).eval w = false := by
    rw [← suppression_as_slot C j hj]
    exact hc.2
  exact (slot_critical_value _ _ _ _ w
    (by rw [circuit_as_slot C j hj]; exact hp) hs).2

theorem input_and_pair_true {n : ℕ} (pre : List Gate) (a b : Fin n) :
    preValue pre (inputAnd a b) (doubleRow a b) = true := by
  rw [input_and_value pre a b _ (by simp [doubleRow])]
  simp [doubleRow,List.getD_eq_getElem?_getD,a.isLt,b.isLt]

theorem input_and_clean (N : ℕ) (I : Fin N → Fin N → Prop) (pre : List Gate)
    (p l : Fin N) (hi : I p l) (q m : Fin N) (hn : ¬ I q m) :
    preValue pre (inputAnd (Fin.castAdd N p) (Fin.natAdd N l))
      (doubleRow (Fin.castAdd N q) (Fin.natAdd N m)) = false := by
  rw [input_and_value _ _ _ _ (by simp [doubleRow])]
  cases he : ((doubleRow (Fin.castAdd N q) (Fin.natAdd N m)).getD
      (Fin.castAdd N p).val false &&
      (doubleRow (Fin.castAdd N q) (Fin.natAdd N m)).getD
        (Fin.natAdd N l).val false) with
  | false => rfl
  | true =>
    have hp : Fin.castAdd N p = Fin.castAdd N q ∨ Fin.castAdd N p = Fin.natAdd N m := by
      simpa [doubleRow,List.getD_eq_getElem?_getD,(Fin.castAdd N p).isLt,
        (Fin.natAdd N l).isLt] using (Bool.and_eq_true.mp he).1
    have hl : Fin.natAdd N l = Fin.castAdd N q ∨ Fin.natAdd N l = Fin.natAdd N m := by
      simpa [doubleRow,List.getD_eq_getElem?_getD,(Fin.castAdd N p).isLt,
        (Fin.natAdd N l).isLt] using (Bool.and_eq_true.mp he).2
    have ep : p = q := by
      apply Fin.ext
      exact congrArg (fun k : Fin (N+N) => k.val)
        (hp.resolve_right (point_line_distinct N p m))
    have el : l = m := by
      apply Fin.ext
      have hh := congrArg (fun k : Fin (N+N) => k.val)
        (hl.resolve_left (Ne.symm (point_line_distinct N q l)))
      simp only [Fin.val_natAdd] at hh
      omega
    exact False.elim (hn (ep ▸ el ▸ hi))

/-- The all-critical case can be reduced further: if one dirty
    gate has exactly one critical edge, strict progress is possible. -/
theorem unique_critical_progress (N : ℕ) (I : Fin N → Fin N → Prop)
    (C : Circuit) (j : ℕ) (p₀ l₀ p l : Fin N)
    (h : Admissible N I C) (hd : (j,p₀,l₀) ∈ dirtySites N I C)
    (hc : CriticalPair N I C j p l)
    (hunique : ∀ q m, CriticalPair N I C j q m → q = p ∧ m = l) :
    ∃ D : Circuit, Admissible N I D ∧ D.size ≤ C.size ∧
      (dirtySites N I D).card < (dirtySites N I C).card := by
  have hj := ((mem_dirtySites N I C j p₀ l₀).mp hd).1
  let a := Fin.castAdd N p
  let b := Fin.natAdd N l
  let r := inputAnd a b
  apply replace_progress N I C j r p₀ l₀ h hd rfl (by simp [r,inputAnd])
  · intro i hi
    change i ∈ [a.val,b.val] at hi
    simp only [List.mem_cons,List.mem_singleton] at hi
    rcases hi with rfl | rfl
    · have hh := a.isLt
      omega
    · have hh := b.isLt
      omega
  · intro w hw hv
    change preValue (C.gates.take j) (inputAnd a b) w = true at hv
    rw [input_and_value _ _ _ _ hw] at hv
    have hb := pair_below_list a b w hw (Bool.and_eq_true.mp hv).1 (Bool.and_eq_true.mp hv).2
    exact original_slot_mono C j hj h.1 _ _ hb (critical_pair_slot_true N I C j hj h p l hc)
  · intro q m hq
    obtain ⟨rfl,rfl⟩ := hunique q m hq
    exact input_and_pair_true _ a b
  · intro q m hn
    exact input_and_clean N I _ p l hc.1 q m hn

end PEqualNP.Outside.L_meta_3457_single_critical
