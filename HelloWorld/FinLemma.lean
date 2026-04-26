import Mathlib.Data.List.Perm.Subperm
import Mathlib.Data.List.FinRange

-- ============================================================
-- MAIN LEMMA: A Nodup list of Fin n values has length <= n.
-- Every element of xs is in `List.finRange n` (which has length n),
-- so xs is a subperm of finRange n and hence xs.length ≤ n.
-- ============================================================
theorem nodup_fin_length_le {n : Nat} (xs : List (Fin n)) (h : xs.Nodup) :
    xs.length ≤ n := by
  have := (List.Nodup.subperm h (fun x _ => List.mem_finRange x)).length_le
  simpa using this
