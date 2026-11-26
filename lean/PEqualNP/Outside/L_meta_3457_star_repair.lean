import PEqualNP.Outside.L_meta_3457_single_critical

/-!
Strict progress when the critical pairs form a star and the
prefix already contains the OR of its critical leaves.
The hypothesis concerns the actual wire function, not merely
its singleton support (which might hide other AND terms).
-/
namespace PEqualNP.Outside.L_meta_3457_star_repair

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

def wireAnd (a b : ℕ) : Gate := ⟨GateOp.and,[a,b]⟩

theorem wireAnd_value (pre : List Gate) (a b : ℕ) (w : List Bool) :
    preValue pre (wireAnd a b) w =
      ((pre.foldl step w).getD a false && (pre.foldl step w).getD b false) := by
  simp only [preValue,wireAnd,GateOp.eval,List.map_cons,List.map_nil,
    List.all_cons,List.all_nil,id,Bool.and_true]

theorem double_read {n : ℕ} (a b k : Fin n) :
    (doubleRow a b).getD k.val false = true ↔ k = a ∨ k = b := by
  simp [doubleRow,List.getD_eq_getElem?_getD,k.isLt]

theorem point_star_repair (N : ℕ) (I : Fin N → Fin N → Prop)
    (C : Circuit) (j s : ℕ) (p₀ l₀ p : Fin N)
    (h : Admissible N I C) (hd : (j,p₀,l₀) ∈ dirtySites N I C)
    (hs : s < N+N+j)
    (hstar : ∀ q l, CriticalPair N I C j q l → q = p)
    (hwire : ∀ w : List Bool, w.length = N+N →
      ((C.gates.take j).foldl step w).getD s false = true ↔
        ∃ l : Fin N, CriticalPair N I C j p l ∧
          w.getD (Fin.natAdd N l).val false = true) :
    ∃ D : Circuit, Admissible N I D ∧ D.size ≤ C.size ∧
      (dirtySites N I D).card < (dirtySites N I C).card := by
  have hj := ((mem_dirtySites N I C j p₀ l₀).mp hd).1
  let a := Fin.castAdd N p
  let r := wireAnd a.val s
  have he : ∀ w : List Bool, w.length = N+N →
      (preValue (C.gates.take j) r w = true ↔
        w.getD a.val false = true ∧
          ∃ l : Fin N, CriticalPair N I C j p l ∧
            w.getD (Fin.natAdd N l).val false = true) := by
    intro w hw
    have ha : a.val < w.length := by rw [hw]; exact a.isLt
    rw [wireAnd_value,fold_keep _ _ ha,Bool.and_eq_true,hwire w hw]
  apply replace_progress N I C j r p₀ l₀ h hd rfl (by simp [r,wireAnd])
  · intro i hi
    change i ∈ [a.val,s] at hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl
    · have ha := a.isLt
      omega
    · exact hs
  · intro w hw hv
    obtain ⟨hp,l,hc,hl⟩ := (he w hw).mp hv
    exact original_slot_mono C j hj h.1 _ _
      (pair_below_list a (Fin.natAdd N l) w hw hp hl)
      (critical_pair_slot_true N I C j hj h p l hc)
  · intro q l hc
    have eq := hstar q l hc
    subst q
    let w := doubleRow a (Fin.natAdd N l)
    apply (he w (by simp [w,doubleRow])).mpr
    exact ⟨(double_read a _ a).mpr (Or.inl rfl),
      l,hc,(double_read a _ _).mpr (Or.inr rfl)⟩
  · intro q m hn
    let w := doubleRow (Fin.castAdd N q) (Fin.natAdd N m)
    cases hv : preValue (C.gates.take j) r w with
    | false => rfl
    | true =>
      obtain ⟨hp,l,hc,hl⟩ := (he w (by simp [w,doubleRow])).mp hv
      have hp' := (double_read (Fin.castAdd N q) (Fin.natAdd N m) a).mp hp
      have hl' := (double_read (Fin.castAdd N q) (Fin.natAdd N m) (Fin.natAdd N l)).mp hl
      have ep : p = q := by
        apply Fin.ext
        exact congrArg (fun k : Fin (N+N) => k.val)
          (hp'.resolve_right (point_line_distinct N p m))
      have el : l = m := by
        apply Fin.ext
        have hh := congrArg (fun k : Fin (N+N) => k.val)
          (hl'.resolve_left (Ne.symm (point_line_distinct N q l)))
        simp only [Fin.val_natAdd] at hh
        omega
      exact False.elim (hn (ep ▸ el ▸ hc.1))

end PEqualNP.Outside.L_meta_3457_star_repair
