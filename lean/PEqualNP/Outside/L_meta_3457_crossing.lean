import PEqualNP.Outside.L_meta_3457_cofactor
import PEqualNP.Outside.L_meta_3457_shadow

/-!
Compare three runs of a monotone suffix:
H = a positive row with its critical slot set to true;
L = that same row with the slot set to false;
V = a negative row on which the original slot is true.

A crossing wire is true in H and false in L and V. No crossing
exists in the initial three prefixes. If one exists at the output,
the first crossing must be an AND with two different operands:
one true in H,V and false in L, and one true in H,L and false in V.
This identifies an actual filtering event, not just a later AND.
-/
namespace PEqualNP.Outside.L_meta_3457_crossing

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.Helpers.CoverCircB
open PEqualNP.Outside.L_meta_3457_cover_cut
open PEqualNP.Outside.L_meta_3457_shadow
open PEqualNP.Outside.L_meta_3457_suppress
open PEqualNP.Outside.L_meta_3457_cofactor

def CrossWire (h l v : List Bool) (i : ℕ) : Prop :=
  h.getD i false = true ∧ l.getD i false = false ∧ v.getD i false = false

def NoCross (h l v : List Bool) : Prop :=
  h.length = l.length ∧ h.length = v.length ∧ ∀ i, ¬ CrossWire h l v i

def Filters (h l v : List Bool) (g : Gate) : Prop :=
  g.op = GateOp.and ∧
    ∃ a ∈ g.inputs, ∃ b ∈ g.inputs,
      a ≠ b ∧
      (h.getD a false = true ∧ l.getD a false = false ∧ v.getD a false = true) ∧
      (h.getD b false = true ∧ l.getD b false = true ∧ v.getD b false = false)

def value (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

theorem initial_no_cross (u v : List Bool) (hlen : u.length = v.length) :
    NoCross (u ++ [true]) (u ++ [false]) (v ++ [true]) := by
  refine ⟨by simp,by simp [hlen],?_⟩
  intro i hi
  obtain ⟨hh,hl,hv⟩ := hi
  by_cases hit : i < u.length
  · rw [getD_app_left (w := u) (t := [true]) hit] at hh
    rw [getD_app_left (w := u) (t := [false]) hit] at hl
    rw [hh] at hl
    cases hl
  · have hle : u.length ≤ i := by omega
    rw [getD_tail u [true] i hle] at hh
    rw [getD_tail v [true] i (by omega), ← hlen] at hv
    rw [hh] at hv
    cases hv

theorem no_cross_snoc (h l v : List Bool) (a b c : Bool)
    (hn : NoCross h l v) (hc : ¬ (a = true ∧ b = false ∧ c = false)) :
    NoCross (h ++ [a]) (l ++ [b]) (v ++ [c]) := by
  obtain ⟨hl,hv,hn⟩ := hn
  refine ⟨by simp [hl],by simp [hv],?_⟩
  intro i hi
  obtain ⟨ha,hb,hc'⟩ := hi
  by_cases hit : i < h.length
  · rw [getD_app_left (w := h) (t := [a]) hit] at ha
    rw [getD_app_left (w := l) (t := [b]) (by omega)] at hb
    rw [getD_app_left (w := v) (t := [c]) (by omega)] at hc'
    exact hn i ⟨ha,hb,hc'⟩
  · rw [getD_tail h [a] i (by omega)] at ha
    rw [getD_tail l [b] i (by omega), ← hl] at hb
    rw [getD_tail v [c] i (by omega), ← hv] at hc'
    cases he : i-h.length with
    | zero =>
      exact hc ⟨by simpa [he] using ha,by simpa [he] using hb,by simpa [he] using hc'⟩
    | succ k => simp [he] at ha

theorem crossing_gate_filters (g : Gate) (h l v : List Bool)
    (hn : NoCross h l v) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hh : value h g = true) (hl : value l g = false) (hv : value v g = false) :
    Filters h l v g := by
  classical
  rcases hg with hop | hop
  · have hH : ∀ i ∈ g.inputs, h.getD i false = true := by
      simpa only [value,hop,GateOp.eval,List.all_map,Function.comp_def,List.all_eq_true,id] using hh
    have hL : ∃ a ∈ g.inputs, l.getD a false = false := by
      by_contra hn
      have he : value l g = true := by
        simp only [value,hop,GateOp.eval,List.all_map,Function.comp_def,List.all_eq_true,id]
        intro i hi
        cases he : l.getD i false with
        | true => rfl
        | false => exact False.elim (hn ⟨i,hi,he⟩)
      rw [hl] at he
      cases he
    have hV : ∃ b ∈ g.inputs, v.getD b false = false := by
      by_contra hn
      have he : value v g = true := by
        simp only [value,hop,GateOp.eval,List.all_map,Function.comp_def,List.all_eq_true,id]
        intro i hi
        cases he : v.getD i false with
        | true => rfl
        | false => exact False.elim (hn ⟨i,hi,he⟩)
      rw [hv] at he
      cases he
    obtain ⟨a,ha,haL⟩ := hL
    obtain ⟨b,hb,hbV⟩ := hV
    have haV : v.getD a false = true := by
      cases he : v.getD a false with
      | true => rfl
      | false => exact False.elim (hn.2.2 a ⟨hH a ha,haL,he⟩)
    have hbL : l.getD b false = true := by
      cases he : l.getD b false with
      | true => rfl
      | false => exact False.elim (hn.2.2 b ⟨hH b hb,he,hbV⟩)
    refine ⟨hop,a,ha,b,hb,?_,⟨hH a ha,haL,haV⟩,⟨hH b hb,hbL,hbV⟩⟩
    intro he
    subst b
    rw [haL] at hbL
    cases hbL
  · have hH : ∃ i ∈ g.inputs, h.getD i false = true := by
      simpa only [value,hop,GateOp.eval,List.any_map,Function.comp_def,List.any_eq_true,id] using hh
    obtain ⟨i,hi,hH⟩ := hH
    have hL : l.getD i false = false := by
      cases he : l.getD i false with
      | false => rfl
      | true =>
        have ht : value l g = true := by
          simp only [value,hop,GateOp.eval,List.any_map,Function.comp_def,List.any_eq_true,id]
          exact ⟨i,hi,he⟩
        rw [hl] at ht
        cases ht
    have hV : v.getD i false = false := by
      cases he : v.getD i false with
      | false => rfl
      | true =>
        have ht : value v g = true := by
          simp only [value,hop,GateOp.eval,List.any_map,Function.comp_def,List.any_eq_true,id]
          exact ⟨i,hi,he⟩
        rw [hv] at ht
        cases ht
    exact False.elim (hn.2.2 i ⟨hH,hL,hV⟩)

/-- The first crossing appears at an actual filtering AND. -/
theorem crossing_exists (gs : List Gate) (h l v : List Bool)
    (hm : MonoList gs) (hn : NoCross h l v)
    (o : ℕ) (ho : CrossWire (gs.foldl step h) (gs.foldl step l) (gs.foldl step v) o) :
    ∃ pre post : List Gate, ∃ g : Gate, gs = pre ++ g :: post ∧
      Filters (pre.foldl step h) (pre.foldl step l) (pre.foldl step v) g := by
  classical
  induction gs generalizing h l v with
  | nil => exact False.elim (hn.2.2 o ho)
  | cons g gs ih =>
    have hgm := hm g (by simp)
    by_cases hc : value h g = true ∧ value l g = false ∧ value v g = false
    · exact ⟨[],gs,g,rfl,crossing_gate_filters g h l v hn hgm hc.1 hc.2.1 hc.2.2⟩
    · have hnext : NoCross (step h g) (step l g) (step v g) :=
        no_cross_snoc h l v _ _ _ hn hc
      have hmt : MonoList gs := fun a ha => hm a (List.mem_cons_of_mem _ ha)
      obtain ⟨pre,post,k,he,hf⟩ := ih (step h g) (step l g) (step v g) hmt hnext ho
      exact ⟨g::pre,post,k,congrArg (List.cons g) he,hf⟩

theorem critical_slot_filter (pre post : List Gate) (g : Gate) (o : ℕ)
    (u v : List Bool) (hlen : u.length = v.length)
    (hm : MonoList post)
    (hpositive : (slot pre post g o).eval u = true)
    (hlow : (slot pre post zeroGate o).eval u = false)
    (hnegative : (slot pre post g o).eval v = false)
    (hdirty : preValue pre g v = true) :
    ∃ before after : List Gate, ∃ k : Gate, post = before ++ k :: after ∧
      Filters (before.foldl step ((pre.foldl step u) ++ [true]))
        (before.foldl step ((pre.foldl step u) ++ [false]))
        (before.foldl step ((pre.foldl step v) ++ [true])) k := by
  have hs := (slot_critical_value pre post g o u hpositive hlow).1
  have hn : NoCross ((pre.foldl step u) ++ [true])
      ((pre.foldl step u) ++ [false]) ((pre.foldl step v) ++ [true]) :=
    initial_no_cross _ _ (by simp only [fold_length,hlen])
  have hV : high pre post o v = false := by
    rw [slot_eval_mux,hdirty,if_true] at hnegative
    exact hnegative
  exact crossing_exists post _ _ _ hm hn o ⟨hs.2,hs.1,hV⟩

end PEqualNP.Outside.L_meta_3457_crossing
