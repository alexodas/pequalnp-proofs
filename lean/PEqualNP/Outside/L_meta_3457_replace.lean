import PEqualNP.Outside.L_meta_3457_or_suffix

/-!
A downward gate replacement with the same gate kind. If it
retains all critical positive pairs and is false on negative pairs,
it yields strict progress in the dirty-site potential.
-/
namespace PEqualNP.Outside.L_meta_3457_replace

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.MetaComplexity.Helpers.CoverCircB
open PEqualNP.Outside.L_meta_3457_cover_cut
open PEqualNP.Outside.L_meta_3457_shadow
open PEqualNP.Outside.L_meta_3457_first_gate
open PEqualNP.Outside.L_meta_3457_suppress
open PEqualNP.Outside.L_meta_3457_critical_cut
open PEqualNP.Outside.L_meta_3457_essential_cut
open PEqualNP.Outside.L_meta_3457_cofactor
open PEqualNP.Outside.L_meta_3457_or_suffix

def replaceGate (C : Circuit) (j : ℕ) (r : Gate) : Circuit :=
  ⟨C.gates.set j r,C.output⟩

theorem replace_as_slot (C : Circuit) (j : ℕ) (r : Gate)
    (hj : j < C.gates.length) :
    replaceGate C j r = slot (C.gates.take j) (C.gates.drop (j+1)) r C.output := by
  unfold replaceGate slot
  rw [gate_set_split C.gates j r hj]

theorem replace_size (C : Circuit) (j : ℕ) (r : Gate) :
    (replaceGate C j r).size = C.size := by simp [replaceGate,Circuit.size]

theorem replace_at_self (C : Circuit) (j : ℕ) (r : Gate) (hj : j < C.gates.length) :
    gateAt (replaceGate C j r) j = r := by
  simp only [gateAt, replaceGate, List.getD_eq_getElem?_getD,
    List.getElem?_set_self hj, Option.getD_some]

theorem replace_at_other (C : Circuit) (j k : ℕ) (r : Gate) (h : j ≠ k) :
    gateAt (replaceGate C j r) k = gateAt C k := by
  simp only [gateAt, replaceGate, List.getD_eq_getElem?_getD, List.getElem?_set_ne h]

theorem replace_monotone (C : Circuit) (j : ℕ) (r : Gate) (hm : Monotone2 C)
    (hop : r.op = GateOp.and ∨ r.op = GateOp.or) (hlen : r.inputs.length ≤ 2) :
    Monotone2 (replaceGate C j r) := by
  intro g hg
  change g ∈ C.gates.set j r at hg
  rcases List.mem_or_eq_of_mem_set hg with h | rfl
  · exact hm g h
  · exact ⟨by simpa using hop,hlen⟩

theorem replace_reads_back (n : ℕ) (C : Circuit) (j : ℕ) (r : Gate)
    (hr : ReadsBack n C) (hback : ∀ i ∈ r.inputs, i < n+j) :
    ReadsBack n (replaceGate C j r) := by
  intro k hk i hi
  have hk' : k < C.gates.length := by simpa [replaceGate] using hk
  by_cases he : j = k
  · subst k
    rw [replace_at_self C j r hk'] at hi
    exact hback i hi
  · rw [replace_at_other C j k r he] at hi
    exact hr k hk' i hi

theorem replace_same_op (C : Circuit) (j k : ℕ) (r : Gate)
    (hj : j < C.gates.length) (hop : r.op = (gateAt C j).op) :
    (gateAt (replaceGate C j r) k).op = (gateAt C k).op := by
  by_cases h : j = k
  · subst k
    rw [replace_at_self C j r hj]
    exact hop
  · rw [replace_at_other C j k r h]

theorem suffix_mono (C : Circuit) (hm : Monotone2 C) (j : ℕ) :
    MonoList (C.gates.drop (j+1)) := by
  intro g hg
  have h : g ∈ C.gates := List.mem_of_mem_drop hg
  simpa using (hm g h).1

theorem slot_wires (pre post : List Gate) (g : Gate) (o : ℕ) (w : List Bool) :
    (slot pre post g o).wires w =
      post.foldl step ((pre.foldl step w) ++ [preValue pre g w]) := by
  simp only [slot,wires_eq,List.foldl_append,List.foldl_cons,step,preValue]

theorem replace_wires_below (C : Circuit) (j : ℕ) (r : Gate)
    (hj : j < C.gates.length) (hm : Monotone2 C) (w : List Bool)
    (h : preValue (C.gates.take j) r w = true →
      preValue (C.gates.take j) (atGate C.gates j) w = true) :
    Below ((replaceGate C j r).wires w) (C.wires w) := by
  rw [replace_as_slot C j r hj, ← circuit_as_slot C j hj, slot_wires, slot_wires]
  exact fold_below _ _ _ (below_snoc _ _ _ _ (below_refl _) h) (suffix_mono C hm j)

theorem replace_slot_value (C : Circuit) (j : ℕ) (r : Gate)
    (hj : j < C.gates.length) (w : List Bool) :
    ((replaceGate C j r).wires w).getD (w.length+j) false =
      preValue (C.gates.take j) r w := by
  rw [replace_as_slot C j r hj, slot_wires]
  have hlen : (List.foldl step w (C.gates.take j)).length = w.length+j := by
    rw [fold_length,List.length_take,Nat.min_eq_left (Nat.le_of_lt hj)]
  have h : w.length+j < ((C.gates.take j).foldl step w ++
      [preValue (C.gates.take j) r w]).length := by simp [hlen]
  rw [fold_keep _ _ h]
  rw [getD_tail _ _ _ (by omega),hlen,Nat.sub_self]
  rfl

def CriticalPair (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
    (j : ℕ) (p l : Fin N) : Prop :=
  I p l ∧ (suppress C j).eval (doubleRow (Fin.castAdd N p) (Fin.natAdd N l)) = false

theorem replace_preserves_positive (N : ℕ) (I : Fin N → Fin N → Prop)
    (C : Circuit) (j : ℕ) (r : Gate) (hj : j < C.gates.length)
    (h : Admissible N I C)
    (hcrit : ∀ p l : Fin N, CriticalPair N I C j p l →
      preValue (C.gates.take j) r (doubleRow (Fin.castAdd N p) (Fin.natAdd N l)) = true)
    (p l : Fin N) (hi : I p l) :
    (replaceGate C j r).eval (doubleRow (Fin.castAdd N p) (Fin.natAdd N l)) = true := by
  let w := doubleRow (Fin.castAdd N p) (Fin.natAdd N l)
  have hpos : C.eval w = true := by
    apply (h.2.2.1 (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l))).mpr
    exact ⟨p,l,hi,by simp,by simp⟩
  have hs := circuit_as_slot C j hj
  rw [replace_as_slot C j r hj]
  apply (slot_preserves_positive_iff (C.gates.take j) (C.gates.drop (j+1))
    (atGate C.gates j) r C.output w (suffix_mono C h.1 j) (by simpa only [hs] using hpos)).mpr
  intro hlo
  apply hcrit p l
  refine ⟨hi,?_⟩
  rw [suppression_as_slot C j hj,slot_zero_eval]
  exact hlo

/-- A one-slot replacement of an AND with a lower, clean AND
    that retains all its critical pairs is an admissible strict step. -/
theorem replace_progress_at (N : ℕ) (I : Fin N → Fin N → Prop)
    (C : Circuit) (j : ℕ) (r : Gate) (p₀ l₀ : Fin N)
    (h : Admissible N I C) (hd : (j,p₀,l₀) ∈ dirtySites N I C)
    (hop : r.op = GateOp.and) (hlen : r.inputs.length ≤ 2)
    (hback : ∀ i ∈ r.inputs, i < N+N+j)
    (hlower : ∀ w : List Bool, w.length = N+N →
      preValue (C.gates.take j) r w = true →
        preValue (C.gates.take j) (atGate C.gates j) w = true)
    (hcrit : ∀ p l : Fin N, CriticalPair N I C j p l →
      preValue (C.gates.take j) r (doubleRow (Fin.castAdd N p) (Fin.natAdd N l)) = true)
    (hclean : preValue (C.gates.take j) r
      (doubleRow (Fin.castAdd N p₀) (Fin.natAdd N l₀)) = false) :
    ∃ D : Circuit, Admissible N I D ∧ D.size ≤ C.size ∧
      (dirtySites N I D).card < (dirtySites N I C).card := by
  obtain ⟨hj,hn,hjop,hval⟩ := (mem_dirtySites N I C j p₀ l₀).mp hd
  let D := replaceGate C j r
  have hm : Monotone2 D := replace_monotone C j r h.1 (Or.inl hop) hlen
  have hr : ReadsBack (N+N) D := replace_reads_back _ C j r h.2.1 hback
  have hop' : r.op = (gateAt C j).op := hop.trans hjop.symm
  have hb : ∀ w : List Bool, w.length = N+N → Below (D.wires w) (C.wires w) :=
    fun w hw => replace_wires_below C j r hj h.1 w (hlower w hw)
  have hf : ∀ z : Fin (N+N) → Bool, D.eval (List.ofFn z) = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true := by
    intro z
    constructor
    · intro he
      apply (h.2.2.1 z).mp
      exact (hb (List.ofFn z) (by simp)).2 C.output he
    · rintro ⟨p,l,hi,hp,hl⟩
      exact eval_upward D hm _ _ (pair_below_input _ _ z hp hl)
        (replace_preserves_positive N I C j r hj h hcrit p l hi)
  have hs : ∀ k < D.gates.length, (gateAt D k).op = GateOp.and →
      ∀ i : Fin (N+N), (D.wires (singletonRow i)).getD (N+N+k) false = false := by
    intro k hk ho i
    have hk' : k < C.gates.length := by simpa [D,replaceGate] using hk
    have ho' : (gateAt C k).op = GateOp.and := (replace_same_op C j k r hj hop').symm.trans ho
    have he := h.2.2.2 k hk' ho' i
    cases hv : (D.wires (singletonRow i)).getD (N+N+k) false with
    | false => rfl
    | true =>
      have hh := (hb (singletonRow i) (by simp [singletonRow])).2 _ hv
      rw [he] at hh
      cases hh
  have hsub : dirtySites N I D ⊆ dirtySites N I C := by
    rintro ⟨k,p,l⟩ he
    obtain ⟨hk,hi,ho,hv⟩ := (mem_dirtySites N I D k p l).mp he
    have hk' : k < C.gates.length := by simpa [D,replaceGate] using hk
    have ho' : (gateAt C k).op = GateOp.and := (replace_same_op C j k r hj hop').symm.trans ho
    exact (mem_dirtySites N I C k p l).mpr ⟨hk',hi,ho',
      (hb _ (by simp [doubleRow])).2 _ hv⟩
  have hnot : (j,p₀,l₀) ∉ dirtySites N I D := by
    intro he
    obtain ⟨_,_,_,hv⟩ := (mem_dirtySites N I D j p₀ l₀).mp he
    let w := doubleRow (Fin.castAdd N p₀) (Fin.natAdd N l₀)
    have hw : w.length = N+N := by simp [w,doubleRow]
    change ((replaceGate C j r).wires w).getD (N+N+j) false = true at hv
    have he := replace_slot_value C j r hj w
    rw [hw] at he
    rw [he,hclean] at hv
    cases hv
  refine ⟨D,⟨hm,hr,hf,hs⟩,le_of_eq (replace_size C j r),?_⟩
  exact Finset.card_lt_card ⟨hsub,fun hback => hnot (hback hd)⟩

/-- Full cleaning is sufficient, but eliminating one dirty site is enough. -/
theorem replace_progress (N : ℕ) (I : Fin N → Fin N → Prop)
    (C : Circuit) (j : ℕ) (r : Gate) (p₀ l₀ : Fin N)
    (h : Admissible N I C) (hd : (j,p₀,l₀) ∈ dirtySites N I C)
    (hop : r.op = GateOp.and) (hlen : r.inputs.length ≤ 2)
    (hback : ∀ i ∈ r.inputs, i < N+N+j)
    (hlower : ∀ w : List Bool, w.length = N+N →
      preValue (C.gates.take j) r w = true →
        preValue (C.gates.take j) (atGate C.gates j) w = true)
    (hcrit : ∀ p l : Fin N, CriticalPair N I C j p l →
      preValue (C.gates.take j) r (doubleRow (Fin.castAdd N p) (Fin.natAdd N l)) = true)
    (hclean : ∀ p l : Fin N, ¬ I p l →
      preValue (C.gates.take j) r (doubleRow (Fin.castAdd N p) (Fin.natAdd N l)) = false) :
    ∃ D : Circuit, Admissible N I D ∧ D.size ≤ C.size ∧
      (dirtySites N I D).card < (dirtySites N I C).card := by
  exact replace_progress_at N I C j r p₀ l₀ h hd hop hlen hback hlower hcrit
    (hclean p₀ l₀ ((mem_dirtySites N I C j p₀ l₀).mp hd).2.1)

end PEqualNP.Outside.L_meta_3457_replace
