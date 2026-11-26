import PEqualNP.Outside.L_meta_3457_star_repair

/-!
Partial cleaning by narrowing one operand to a mandatory endpoint.
Unlike the exact star-union repair, this does not require an
already available union of the critical leaves. It only removes
dirty sites not containing the mandatory endpoint.
-/
namespace PEqualNP.Outside.L_meta_3457_narrow

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.MetaComplexity.Helpers.CoverCircB
open PEqualNP.Outside.L_meta_3457_cover_cut
open PEqualNP.Outside.L_meta_3457_shadow
open PEqualNP.Outside.L_meta_3457_suppress
open PEqualNP.Outside.L_meta_3457_critical_cut
open PEqualNP.Outside.L_meta_3457_essential_cut
open PEqualNP.Outside.L_meta_3457_cofactor
open PEqualNP.Outside.L_meta_3457_replace
open PEqualNP.Outside.L_meta_3457_single_critical
open PEqualNP.Outside.L_meta_3457_star_repair

theorem singleton_below_list {n : ℕ} (k : Fin n) (w : List Bool)
    (hw : w.length = n) (hk : w.getD k.val false = true) :
    Below (singletonRow k) w := by
  refine ⟨by simp [singletonRow,hw],?_⟩
  intro i hi
  by_cases h : i < n
  · have he : (⟨i,h⟩ : Fin n) = k := by
      simpa [singletonRow,List.getD_eq_getElem?_getD,h] using hi
    have hv : i = k.val := congrArg Fin.val he
    rw [hv]
    exact hk
  · simp [singletonRow,List.getD_eq_getElem?_getD,h] at hi

theorem prefix_mono (C : Circuit) (j : ℕ) (hm : Monotone2 C) :
    MonoList (C.gates.take j) := by
  intro g hg
  simpa using (hm g (List.mem_of_mem_take hg)).1

theorem narrow_operand_value (pre : List Gate) {n : ℕ} (k : Fin n)
    (b : ℕ) (w : List Bool) (hw : w.length = n) :
    preValue pre (wireAnd k.val b) w =
      (w.getD k.val false && (pre.foldl step w).getD b false) := by
  have hk : k.val < w.length := by rw [hw]; exact k.isLt
  rw [wireAnd_value,fold_keep pre w hk]

/-- The original AND is lowered by replacing an operand that
    accepts a singleton by the corresponding input variable.
    A shared critical endpoint ensures no critical pair is lost. -/
theorem narrow_operand_progress (N : ℕ) (I : Fin N → Fin N → Prop)
    (C : Circuit) (j a b : ℕ) (p₀ l₀ : Fin N) (k : Fin (N+N))
    (h : Admissible N I C) (hd : (j,p₀,l₀) ∈ dirtySites N I C)
    (hab : (atGate C.gates j).inputs = [a,b])
    (ha : ((C.gates.take j).foldl step (singletonRow k)).getD a false = true)
    (hmandatory : ∀ p l, CriticalPair N I C j p l →
      k = Fin.castAdd N p ∨ k = Fin.natAdd N l)
    (havoid : k ≠ Fin.castAdd N p₀ ∧ k ≠ Fin.natAdd N l₀) :
    ∃ D : Circuit, Admissible N I D ∧ D.size ≤ C.size ∧
      (dirtySites N I D).card < (dirtySites N I C).card := by
  obtain ⟨hj,_,hop,_⟩ := (mem_dirtySites N I C j p₀ l₀).mp hd
  let pre := C.gates.take j
  let r := wireAnd k.val b
  have hback : b < N+N+j := h.2.1 j hj b (by
    change b ∈ (atGate C.gates j).inputs
    rw [hab]
    simp)
  have hold : ∀ w : List Bool, preValue pre (atGate C.gates j) w =
      ((pre.foldl step w).getD a false && (pre.foldl step w).getD b false) := by
    intro w
    simp only [preValue,hop,hab,GateOp.eval,List.map_cons,List.map_nil,
      List.all_cons,List.all_nil,id,Bool.and_true]
  have hnew : ∀ w : List Bool, w.length = N+N →
      preValue pre r w = (w.getD k.val false && (pre.foldl step w).getD b false) :=
    fun w hw => narrow_operand_value pre k b w hw
  apply replace_progress_at N I C j r p₀ l₀ h hd rfl (by simp [r,wireAnd])
  · intro i hi
    change i ∈ [k.val,b] at hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl
    · have hk := k.isLt
      omega
    · exact hback
  · intro w hw hv
    change preValue pre r w = true at hv
    rw [hnew w hw] at hv
    have hk := (Bool.and_eq_true.mp hv).1
    have hb := (Bool.and_eq_true.mp hv).2
    have hbelow := fold_below pre _ _ (singleton_below_list k w hw hk)
      (prefix_mono C j h.1)
    change preValue pre (atGate C.gates j) w = true
    rw [hold]
    exact Bool.and_eq_true.mpr ⟨hbelow.2 a ha,hb⟩
  · intro p l hc
    let w := doubleRow (Fin.castAdd N p) (Fin.natAdd N l)
    have hw : w.length = N+N := by simp [w,doubleRow]
    have hv := critical_pair_slot_true N I C j hj h p l hc
    change preValue pre (atGate C.gates j) w = true at hv
    rw [hold] at hv
    change preValue pre r w = true
    rw [hnew w hw]
    exact Bool.and_eq_true.mpr
      ⟨(double_read _ _ k).mpr (hmandatory p l hc),(Bool.and_eq_true.mp hv).2⟩
  · let w := doubleRow (Fin.castAdd N p₀) (Fin.natAdd N l₀)
    have hw : w.length = N+N := by simp [w,doubleRow]
    change preValue pre r w = false
    rw [hnew w hw]
    have hk : w.getD k.val false = false := by
      cases he : w.getD k.val false with
      | false => rfl
      | true =>
        rcases (double_read _ _ k).mp he with he | he
        · exact False.elim (havoid.1 he)
        · exact False.elim (havoid.2 he)
    simp [hk]


/-- In a least-dirty representative, every dirty pair contains
    each mandatory critical endpoint that is accepted by the
    first operand on its singleton row. -/
theorem minimal_dirty_contains_mandatory (N : ℕ) (I : Fin N → Fin N → Prop)
    (C : Circuit) (h : Admissible N I C)
    (hmin : ∀ D : Circuit, Admissible N I D → D.size ≤ C.size →
      (dirtySites N I C).card ≤ (dirtySites N I D).card)
    (j a b : ℕ) (p₀ l₀ : Fin N) (k : Fin (N+N))
    (hd : (j,p₀,l₀) ∈ dirtySites N I C)
    (hab : (atGate C.gates j).inputs = [a,b])
    (ha : ((C.gates.take j).foldl step (singletonRow k)).getD a false = true)
    (hmandatory : ∀ p l, CriticalPair N I C j p l →
      k = Fin.castAdd N p ∨ k = Fin.natAdd N l) :
    k = Fin.castAdd N p₀ ∨ k = Fin.natAdd N l₀ := by
  classical
  by_contra hn
  have hav : k ≠ Fin.castAdd N p₀ ∧ k ≠ Fin.natAdd N l₀ :=
    ⟨fun he => hn (Or.inl he),fun he => hn (Or.inr he)⟩
  obtain ⟨D,hD,hs,hlt⟩ :=
    narrow_operand_progress N I C j a b p₀ l₀ k h hd hab ha hmandatory hav
  exact (Nat.not_lt_of_ge (hmin D hD hs)) hlt

end PEqualNP.Outside.L_meta_3457_narrow
