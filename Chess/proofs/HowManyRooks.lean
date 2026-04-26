import ChessRules
import Mathlib.Data.List.Perm.Subperm
import Mathlib.Data.List.FinRange

-- ============================================================
-- LEMMA: A Nodup list of Fin n values has length <= n.
-- Every element of xs is in `List.finRange n` (which has length n),
-- so xs is a subperm of finRange n and hence xs.length ≤ n.
-- ============================================================
theorem nodup_fin_length_le {n : Nat} (xs : List (Fin n)) (h : xs.Nodup) :
    xs.length ≤ n := by
  have := (List.Nodup.subperm h (fun x _ => List.mem_finRange x)).length_le
  simpa using this


-- ============================================================
-- PROOF: at most n non-attacking rooks on an n x n board
-- ============================================================
def nonAttackingRooks {n : Nat} (ps : List (Fin n × Fin n)) : Prop :=
  ∀ p q, p ∈ ps → q ∈ ps → p ≠ q → p.1 ≠ q.1


theorem row_nodup {n : Nat} {ps : List (Fin n × Fin n)}
    (hna : nonAttackingRooks ps) (hnd : ps.Nodup) :
    (ps.map (·.1)).Nodup := by
  induction ps with
  | nil => simp
  | cons p rest ih =>
    rw [List.nodup_cons] at hnd
    obtain ⟨hnotmem, hrest_nd⟩ := hnd
    simp only [List.map_cons, List.nodup_cons]
    constructor
    · intro hmem
      rw [List.mem_map] at hmem
      obtain ⟨q, hq_in, hq_row⟩ := hmem
      have hpq : p ≠ q := fun heq => hnotmem (heq ▸ hq_in)
      exact (hna p q (List.mem_cons.mpr (.inl rfl))
                     (List.mem_cons.mpr (.inr hq_in)) hpq) hq_row.symm
    · apply ih
      · intro a b ha hb hab
        exact hna a b (List.mem_cons.mpr (.inr ha))
                      (List.mem_cons.mpr (.inr hb)) hab
      · exact hrest_nd


theorem rooks_le {n : Nat} (ps : List (Fin n × Fin n))
    (hnd : ps.Nodup) (hna : nonAttackingRooks ps) :
    ps.length <= n := by
  have h1 : (ps.map (·.1)).Nodup := row_nodup hna hnd
  have h2 : (ps.map (·.1)).length <= n := nodup_fin_length_le _ h1
  rwa [List.length_map] at h2


theorem rooks_le_four (ps : List (Pos 4))
    (hnd : ps.Nodup) (hna : nonAttackingRooks ps) :
    ps.length <= 4 :=
  rooks_le ps hnd hna
