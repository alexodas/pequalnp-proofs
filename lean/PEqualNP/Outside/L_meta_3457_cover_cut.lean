import PEqualNP.MetaComplexity.Helpers.CoverCircB2
import PEqualNP.Defs

/-!
Research for L-meta-3457, clean upstream base.
A cover circuit's AND gates are all pointwise below its output.
This establishes the semantic part of the constructive half of a
possible counting cut; the lower bound is not assumed or asserted.
-/

namespace PEqualNP.Outside.L_meta_3457_cover_cut

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers.CoverCircB
open PEqualNP.MetaComplexity.NestedCover

def atGate (gs : List Gate) (j : ℕ) : Gate :=
  gs.getD j ⟨GateOp.or, []⟩

theorem at_append_left (gs hs : List Gate) (j : ℕ)
    (hj : j < gs.length) :
    atGate (gs ++ hs) j = atGate gs j := by
  simp only [atGate, List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

theorem at_append_right (gs hs : List Gate) (j : ℕ)
    (hj : gs.length ≤ j) :
    atGate (gs ++ hs) j = atGate hs (j - gs.length) := by
  simp only [atGate, List.getD_eq_getElem?_getD, List.getElem?_append_right hj]

/-- A block contains exactly one AND, immediately after its OR chain. -/
theorem block_and_index (B a t v : ℕ) (rs : List ℕ) (lead : Bool)
    (j : ℕ) (hj : j < (blockGates B a t v rs lead).length)
    (ha : (atGate (blockGates B a t v rs lead) j).op = GateOp.and) :
    j = rs.length := by
  let os : List Gate := (List.range rs.length).map (fun i =>
    ⟨GateOp.or, [(v :: (List.range rs.length).map (fun k => B + k)).getD i 0,
      rs.getD i 0]⟩)
  let tail : List Gate := ⟨GateOp.and,
    [t, (v :: (List.range rs.length).map (fun k => B + k)).getD rs.length 0]⟩ ::
    (if lead then [] else [⟨GateOp.or, [a, B + rs.length]⟩])
  have hos : os.length = rs.length := by simp [os]
  change (atGate (os ++ tail) j).op = GateOp.and at ha
  by_cases hlt : j < rs.length
  · rw [at_append_left os tail j (by omega)] at ha
    simp [atGate, os, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hlt] at ha
  · rw [at_append_right os tail j (by omega), hos] at ha
    by_contra hne
    have hd : j - rs.length = 1 := by
      rw [block_length] at hj
      cases lead <;> simp at hj <;> omega
    rw [hd] at ha
    cases lead <;> simp [atGate, tail] at ha

theorem block_and_value (w : List Bool) (B a t v : ℕ)
    (rs : List ℕ) (lead : Bool) (hw : w.length = B)
    (ht : t < B) (hv : v < B) (hrs : ∀ u ∈ rs, u < B) :
    ((blockGates B a t v rs lead).foldl step w).getD
        (B + rs.length) false =
      (w.getD t false && (w.getD v false || rs.any (fun u => w.getD u false))) := by
  have h := block_val w B a t v rs true hw (by simp) ht hv hrs
  have he : B + (blockGates B a t v rs true).length - 1 =
      B + rs.length := by rw [block_length]; simp
  rw [he] at h
  simp only [↓reduceIte] at h
  cases lead with
  | true => exact h
  | false =>
    have heq : blockGates B a t v rs false =
        blockGates B a t v rs true ++ [⟨GateOp.or, [a, B + rs.length]⟩] := by
      simp [blockGates]
    rw [heq, List.foldl_append, fold_keep _ _ (by
      rw [fold_length, hw, block_length]; simp)]
    exact h

/-- Every AND in a sequence of cover blocks implies one of its owner
    terms, regardless of the accumulator wire or the earlier prefix. -/
theorem gates_and_sound (n : ℕ) (x : List Bool) :
    ∀ (own : List (ℕ × List ℕ)) (B : ℕ) (lead : Bool)
      (a : ℕ) (w : List Bool),
      (∀ p ∈ own, p.1 < n ∧ ∀ u ∈ p.2, u < n) →
      w.length = B → n ≤ B →
      (∀ i < n, w.getD i false = x.getD i false) →
      ∀ j < (coverGatesB B lead a own).length,
        (atGate (coverGatesB B lead a own) j).op = GateOp.and →
        ((coverGatesB B lead a own).foldl step w).getD (B + j) false = true →
        F x own = true
  | [], _, _, _, _, _, _, _, _, j, hj, _, _ => by simp [coverGatesB] at hj
  | (t, []) :: os, B, lead, a, w, hown, hw, hn, hx, j, hj, hop, hval => by
    have h := gates_and_sound n x os B lead a w
      (fun p hp => hown p (List.mem_cons_of_mem _ hp)) hw hn hx
      j hj hop hval
    change ((x.getD t false && false) || F x os) = true
    rw [h]
    simp
  | (t, v :: rs) :: os, B, lead, a, w, hown, hw, hn, hx, j, hj, hop, hval => by
    have hp := hown (t, v :: rs) (by simp)
    have ht : t < n := hp.1
    have hv : v < n := hp.2 v (by simp)
    have hrs : ∀ u ∈ rs, u < n := fun u hu => hp.2 u (by simp [hu])
    let bg := blockGates B a t v rs lead
    let tail := coverGatesB (B + bg.length) false (B + bg.length - 1) os
    let W := bg.foldl step w
    have hW : W.length = B + bg.length := by simp [W, fold_length, hw]
    have hWx : ∀ i < n, W.getD i false = x.getD i false := by
      intro i hi
      rw [show W = bg.foldl step w from rfl, fold_keep bg w (by omega)]
      exact hx i hi
    change j < (bg ++ tail).length at hj
    change (atGate (bg ++ tail) j).op = GateOp.and at hop
    change ((bg ++ tail).foldl step w).getD (B + j) false = true at hval
    rw [List.foldl_append] at hval
    change (tail.foldl step W).getD (B + j) false = true at hval
    by_cases hfirst : j < bg.length
    · rw [at_append_left bg tail j hfirst] at hop
      have hidx := block_and_index B a t v rs lead j hfirst hop
      have hkeep : B + j < W.length := by omega
      rw [fold_keep tail W hkeep, hidx] at hval
      have hblock := block_and_value w B a t v rs lead hw
        (by omega : t < B) (by omega : v < B)
        (fun u hu => by have := hrs u hu; omega)
      change W.getD (B + rs.length) false = _ at hblock
      rw [hblock] at hval
      have hr : rs.any (fun u => w.getD u false) =
          rs.any (fun u => x.getD u false) :=
        any_congr_mem (fun u hu => hx u (hrs u hu))
      rw [hx t ht, hx v hv, hr] at hval
      change ((x.getD t false && (x.getD v false || rs.any (fun u => x.getD u false))) || F x os) = true
      rw [hval]
      rfl
    · have hle : bg.length ≤ j := by omega
      rw [at_append_right bg tail j hle] at hop
      have htail : j - bg.length < tail.length := by
        rw [List.length_append] at hj
        omega
      have hidx : B + j = B + bg.length + (j - bg.length) := by omega
      rw [hidx] at hval
      have h := gates_and_sound n x os (B + bg.length) false
        (B + bg.length - 1) W
        (fun p hp => hown p (List.mem_cons_of_mem _ hp)) hW (by omega)
        hWx (j - bg.length) htail hop hval
      change ((x.getD t false && (x.getD v false || rs.any (fun u => x.getD u false))) || F x os) = true
      rw [h]
      simp

/-- A negative input to the complete cover circuit cannot activate
    any of its internal ANDs. -/
theorem cover_ands_below_output (n : ℕ) (own : List (ℕ × List ℕ))
    (hown : ∀ p ∈ own, p.1 < n ∧ ∀ u ∈ p.2, u < n)
    (z : Fin n → Bool) (j : ℕ)
    (hj : j < (coverCircuitB n own).gates.length)
    (hop : (gateAt (coverCircuitB n own) j).op = GateOp.and)
    (hv : ((coverCircuitB n own).wires (List.ofFn z)).getD (n + j) false = true) :
    (coverCircuitB n own).eval (List.ofFn z) = true := by
  have hne : coverGatesB n true 0 own ≠ [] := by
    intro he
    simp [coverCircuitB, he] at hj
  have hg : (coverCircuitB n own).gates = coverGatesB n true 0 own := by
    simp [coverCircuitB, hne]
  rw [hg] at hj
  change (atGate (coverCircuitB n own).gates j).op = GateOp.and at hop
  rw [hg] at hop
  rw [wires_eq, hg] at hv
  have hF := gates_and_sound n (List.ofFn z) own n true 0
    (List.ofFn z) hown (by simp) le_rfl (fun _ _ => rfl) j hj hop hv
  apply (circuit_fun n own hown z).mpr
  simpa [F, List.any_eq_true] using hF


/-- The wire feeding position k of an OR chain already exists. -/
theorem chain_operand_bound (B v : ℕ) (rs : List ℕ) (k : ℕ)
    (hv : v < B) (hk : k ≤ rs.length) :
    (v :: (List.range rs.length).map (fun j => B + j)).getD k 0 < B + k := by
  cases k with
  | zero => simpa using hv
  | succ k =>
    have hkr : k < rs.length := by omega
    have he : (v :: (List.range rs.length).map (fun j => B + j)).getD (k + 1) 0 = B + k := by
      simp [List.getD_cons_succ, List.getD_eq_getElem?_getD, hkr]
    rw [he]
    omega

/-- Each block reads only wires already available at its position. -/
theorem block_reads_back (B a t v : ℕ) (rs : List ℕ) (lead : Bool)
    (ha : lead = false → a < B) (ht : t < B) (hv : v < B)
    (hrs : ∀ u ∈ rs, u < B) :
    ∀ j < (blockGates B a t v rs lead).length,
      ∀ i ∈ (atGate (blockGates B a t v rs lead) j).inputs, i < B + j := by
  intro j hj i hi
  let os : List Gate := (List.range rs.length).map (fun k =>
    ⟨GateOp.or, [(v :: (List.range rs.length).map (fun q => B + q)).getD k 0,
      rs.getD k 0]⟩)
  let tail : List Gate := ⟨GateOp.and,
    [t, (v :: (List.range rs.length).map (fun q => B + q)).getD rs.length 0]⟩ ::
    (if lead then [] else [⟨GateOp.or, [a, B + rs.length]⟩])
  have hos : os.length = rs.length := by simp [os]
  change i ∈ (atGate (os ++ tail) j).inputs at hi
  by_cases hlt : j < rs.length
  · rw [at_append_left os tail j (by omega)] at hi
    have he : atGate os j = ⟨GateOp.or,
        [(v :: (List.range rs.length).map (fun q => B + q)).getD j 0, rs.getD j 0]⟩ := by
      simp [atGate, os, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hlt]
    rw [he] at hi
    simp only [List.mem_cons, List.mem_singleton] at hi
    rcases hi with h | h
    · rw [h]
      exact chain_operand_bound B v rs j hv (by omega)
    · rw [h]
      have hh : rs.getD j 0 = rs[j] := by simp [List.getD_eq_getElem?_getD, hlt]
      rw [hh]
      have := hrs rs[j] (List.getElem_mem hlt)
      omega
  · rw [at_append_right os tail j (by omega), hos] at hi
    by_cases he : j = rs.length
    · subst j
      rw [Nat.sub_self] at hi
      change i ∈ [t, (v :: (List.range rs.length).map (fun q => B + q)).getD rs.length 0] at hi
      simp only [List.mem_cons, List.mem_singleton] at hi
      rcases hi with h | h
      · omega
      · rw [h]
        exact chain_operand_bound B v rs rs.length hv le_rfl
    · have hd : j - rs.length = 1 := by
        rw [block_length] at hj
        cases lead <;> simp at hj <;> omega
      have hl : lead = false := by
        cases lead with
        | false => rfl
        | true =>
          rw [block_length] at hj
          simp at hj
          omega
      rw [hd, hl] at hi
      change i ∈ [a, B + rs.length] at hi
      simp only [List.mem_cons, List.mem_singleton] at hi
      have ha' := ha hl
      rcases hi with h | h <;> omega

theorem gates_reads_back (n : ℕ) :
    ∀ (own : List (ℕ × List ℕ)) (B : ℕ) (lead : Bool) (a : ℕ),
      (∀ p ∈ own, p.1 < n ∧ ∀ u ∈ p.2, u < n) →
      n ≤ B → (lead = false → a < B) →
      ∀ j < (coverGatesB B lead a own).length,
        ∀ i ∈ (atGate (coverGatesB B lead a own) j).inputs, i < B + j
  | [], _, _, _, _, _, _, j, hj, _, _ => by simp [coverGatesB] at hj
  | (t, []) :: os, B, lead, a, hown, hn, ha, j, hj, i, hi =>
    gates_reads_back n os B lead a
      (fun p hp => hown p (List.mem_cons_of_mem _ hp)) hn ha j hj i hi
  | (t, v :: rs) :: os, B, lead, a, hown, hn, ha, j, hj, i, hi => by
    have hp := hown (t, v :: rs) (by simp)
    have ht : t < n := hp.1
    have hv : v < n := hp.2 v (by simp)
    have hrs : ∀ u ∈ rs, u < n := fun u hu => hp.2 u (by simp [hu])
    let bg := blockGates B a t v rs lead
    let tail := coverGatesB (B + bg.length) false (B + bg.length - 1) os
    change j < (bg ++ tail).length at hj
    change i ∈ (atGate (bg ++ tail) j).inputs at hi
    by_cases hfirst : j < bg.length
    · rw [at_append_left bg tail j hfirst] at hi
      exact block_reads_back B a t v rs lead ha (by omega) (by omega)
        (fun u hu => by have := hrs u hu; omega) j hfirst i hi
    · have hle : bg.length ≤ j := by omega
      rw [at_append_right bg tail j hle] at hi
      have hj' : j - bg.length < tail.length := by rw [List.length_append] at hj; omega
      have hbg : 0 < bg.length := by
        change 0 < (blockGates B a t v rs lead).length
        rw [block_length]
        omega
      have hb : 0 < B + bg.length := by omega
      have hh := gates_reads_back n os (B + bg.length) false (B + bg.length - 1)
        (fun p hp => hown p (List.mem_cons_of_mem _ hp)) (by omega)
        (fun _ => by omega) (j - bg.length) hj' i hi
      omega

theorem cover_reads_back (n : ℕ) (own : List (ℕ × List ℕ))
    (hown : ∀ p ∈ own, p.1 < n ∧ ∀ u ∈ p.2, u < n) :
    ReadsBack n (coverCircuitB n own) := by
  intro j hj i hi
  have hne : coverGatesB n true 0 own ≠ [] := by
    intro he
    simp [coverCircuitB, he] at hj
  have hg : (coverCircuitB n own).gates = coverGatesB n true 0 own := by
    simp [coverCircuitB, hne]
  rw [hg] at hj
  change i ∈ (atGate (coverCircuitB n own).gates j).inputs at hi
  rw [hg] at hi
  exact gates_reads_back n own n true 0 hown le_rfl (by simp) j hj i hi

end PEqualNP.Outside.L_meta_3457_cover_cut
