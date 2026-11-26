import PEqualNP.Outside.L_meta_3457_active_budget

/-!
A canonical disjoint star cover when each line has at most one
incident point. The normalization then follows from the number
of essential input variables, with no cleanliness premise on C.
-/
namespace PEqualNP.Outside.L_meta_3457_one_sided

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_3457_active_budget
open PEqualNP.Outside.L_meta_3457_main_cut

variable (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]

def leaves (p : Fin N) : List (Fin N) :=
  (List.finRange N).filter (fun l => decide (I p l))

def centres : List (Fin N) :=
  (List.finRange N).filter (fun p => !(leaves N I p).isEmpty)

def block (p : Fin N) : ℕ × List ℕ :=
  (p.val,(leaves N I p).map (fun l => N+l.val))

def owners : List (ℕ × List ℕ) :=
  (centres N I).map (block N I)

theorem mem_leaves (p l : Fin N) :
    l ∈ leaves N I p ↔ I p l := by
  simp [leaves]

theorem leaves_nodup (p : Fin N) :
    (leaves N I p).Nodup :=
  (List.nodup_finRange N).filter _

theorem centres_nodup : (centres N I).Nodup :=
  (List.nodup_finRange N).filter _

theorem centre_has_leaf (p : Fin N) (hp : p ∈ centres N I) :
    leaves N I p ≠ [] := by
  intro he
  simp [centres,he] at hp

theorem centre_of_incidence (p l : Fin N) (hi : I p l) :
    p ∈ centres N I := by
  have hm := (mem_leaves N I p l).mpr hi
  have hn : leaves N I p ≠ [] := fun he => by rw [he] at hm; simp at hm
  simp [centres,hn]

theorem owners_sound : BlocksSound N I (owners N I) := by
  intro b hb u hu
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hb
  change u ∈ (leaves N I p).map (fun l => N+l.val) at hu
  obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hu
  exact ⟨p,l,(mem_leaves N I p l).mp hl,Or.inl ⟨rfl,rfl⟩⟩

theorem owners_complete : BlocksComplete N I (owners N I) := by
  intro p l hi
  refine ⟨block N I p,List.mem_map.mpr ⟨p,centre_of_incidence N I p l hi,rfl⟩,
    Or.inl ⟨rfl,?_⟩⟩
  exact List.mem_map.mpr ⟨l,(mem_leaves N I p l).mpr hi,rfl⟩

theorem owners_nonempty_blocks :
    ∀ b ∈ owners N I, b.2 ≠ [] := by
  intro b hb
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hb
  simpa [block] using centre_has_leaf N I p hp

theorem block_nodup (p : Fin N) :
    (p.val :: (leaves N I p).map (fun l => N+l.val)).Nodup := by
  apply List.nodup_cons.mpr
  constructor
  · intro h
    obtain ⟨l,_,he⟩ := List.mem_map.mp h
    have hp := p.isLt
    omega
  · apply (leaves_nodup N I p).map
    intro l m he
    apply Fin.ext
    omega

theorem blocks_disjoint
    (hunique : ∀ p q l : Fin N, I p l → I q l → p = q)
    (p q : Fin N) (hpq : p ≠ q) :
    List.Disjoint (p.val :: (leaves N I p).map (fun l => N+l.val))
      (q.val :: (leaves N I q).map (fun l => N+l.val)) := by
  intro t ht hu
  rcases List.mem_cons.mp ht with he | he
  · rcases List.mem_cons.mp hu with hf | hf
    · exact hpq (Fin.ext (he.symm.trans hf))
    · obtain ⟨l,_,hl⟩ := List.mem_map.mp hf
      have hp := p.isLt
      omega
  · obtain ⟨l,hl,he⟩ := List.mem_map.mp he
    rcases List.mem_cons.mp hu with hf | hf
    · have hq := q.isLt
      omega
    · obtain ⟨m,hm,hf⟩ := List.mem_map.mp hf
      have elm : l = m := by
        apply Fin.ext
        omega
      subst m
      exact hpq (hunique p q l ((mem_leaves N I p l).mp hl)
        ((mem_leaves N I q l).mp hm))

theorem owner_vertices_nodup
    (hunique : ∀ p q l : Fin N, I p l → I q l → p = q) :
    (blockVertices (owners N I)).Nodup := by
  unfold blockVertices owners
  rw [List.flatMap_map]
  apply List.nodup_flatMap.mpr
  refine ⟨?_,?_⟩
  · intro p hp
    exact block_nodup N I p
  · exact (centres_nodup N I).imp (fun h => blocks_disjoint N I hunique _ _ h)

/-- Complete normalization for all one-sided star forests. -/
theorem normalize_one_sided
    (hunique : ∀ p q l : Fin N, I p l → I q l → p = q) :
    Normalize N I :=
  disjoint_stars_normalize N I (owners N I) (owners_sound N I)
    (owners_complete N I) (owners_nonempty_blocks N I)
    (owner_vertices_nodup N I hunique)

end PEqualNP.Outside.L_meta_3457_one_sided
