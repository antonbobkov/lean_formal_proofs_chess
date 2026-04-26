-- ============================================================
-- PROOF: nodup_fin_length_le
-- A Nodup list of Fin n values has length <= n.
-- ============================================================


-- ============================================================
-- AUXILIARY LEMMA 1: erasing a present element shrinks length by 1
-- ============================================================
-- `List.erase l a` removes the first occurrence of `a` from `l`.
-- If `a ∈ l` then the result has length exactly l.length - 1.
private theorem length_erase_of_mem [DecidableEq α] {a : α} {l : List α}
    (hmem : a ∈ l) : (l.erase a).length = l.length - 1 := by
  induction l with
  | nil => simp at hmem
  | cons b rest ih =>
    by_cases hab : b = a
    · -- b = a: erase removes the head, leaving `rest`.
      -- After subst, goal is: ((a::rest).erase a).length = (a::rest).length - 1.
      -- Full `simp` knows (a::rest).erase a = rest (a@[simp] lemma).
      subst hab; simp
    · -- b ≠ a: erase skips the head, giving b :: rest.erase a.
      have hmem_rest : a ∈ rest := by
        rcases List.mem_cons.mp hmem with h | h
        · exact absurd h.symm hab   -- h : a = b, hab : b ≠ a
        · exact h
      have hpos : 0 < rest.length := by
        cases rest with
        | nil => simp at hmem_rest
        | cons _ _ => simp
      -- Key step: rewrite (b::rest).erase a to b :: rest.erase a.
      -- We do this as a separate `have` so we can use full `simp`
      -- (which reduces `match false with | true => _ | false => e` to `e`)
      -- then `rw` the result into the main goal.
      have hstep : (b :: rest).erase a = b :: rest.erase a := by
        simp [beq_false_of_ne hab]
      rw [hstep]
      simp only [List.length_cons]
      rw [ih hmem_rest]
      omega


-- ============================================================
-- AUXILIARY LEMMA 2: erasing a different element preserves membership
-- ============================================================
-- If a ≠ b and a ∈ l, then a is still in l after erasing b.
private theorem mem_erase_of_ne [DecidableEq α] {a b : α} {l : List α}
    (hne : a ≠ b) (hmem : a ∈ l) : a ∈ l.erase b := by
  induction l with
  | nil => simp at hmem
  | cons c rest ih =>
    by_cases hcb : c = b
    · -- c = b: erase removes the head c, leaving `rest`.
      subst hcb
      have hstep : (c :: rest).erase c = rest := by simp
      rw [hstep]
      rcases List.mem_cons.mp hmem with h | h
      · exact absurd h hne   -- h : a = c = b, contradicts a ≠ b
      · exact h
    · -- c ≠ b: erase skips the head, giving c :: rest.erase b.
      have hstep : (c :: rest).erase b = c :: rest.erase b := by
        simp [beq_false_of_ne hcb]
      rw [hstep]
      rcases List.mem_cons.mp hmem with h | h
      · exact List.mem_cons.mpr (.inl h)       -- a = c, still the head
      · exact List.mem_cons.mpr (.inr (ih h))  -- a ∈ rest, apply IH


-- ============================================================
-- KEY LEMMA: Nodup subset bound
-- ============================================================
-- `revert`ing ys before the induction makes the IH say
-- "for ALL ys, if rest fits in ys then rest.length ≤ ys.length",
-- allowing us to instantiate it with ys.erase x in the cons step.
private theorem nodup_length_le_of_subset [DecidableEq α] {xs : List α}
    (hnd : xs.Nodup) : ∀ {ys : List α}, (∀ x ∈ xs, x ∈ ys) → xs.length ≤ ys.length := by
  induction xs with
  | nil => intros; simp
  | cons x rest ih =>
    rw [List.nodup_cons] at hnd
    obtain ⟨hxrest, hrest_nd⟩ := hnd
    intro ys hmem
    have hx_ys : x ∈ ys := hmem x (List.mem_cons.mpr (.inl rfl))
    have hrest_in_erase : ∀ y ∈ rest, y ∈ ys.erase x := fun y hy =>
      mem_erase_of_ne
        (fun heq => hxrest (heq ▸ hy))
        (hmem y (List.mem_cons.mpr (.inr hy)))
    have hih  : rest.length ≤ (ys.erase x).length := ih hrest_nd hrest_in_erase
    have hlen : (ys.erase x).length = ys.length - 1  := length_erase_of_mem hx_ys
    have hpos : 0 < ys.length := by
      cases ys with
      | nil => simp at hx_ys
      | cons _ _ => simp
    simp only [List.length_cons]
    omega


-- ============================================================
-- MAIN LEMMA
-- ============================================================
-- Every element of xs : List (Fin n) is in List.finRange n
-- (which has length n), so xs.length ≤ n.
theorem nodup_fin_length_le {n : Nat} (xs : List (Fin n)) (h : xs.Nodup) :
    xs.length ≤ n := by
  have hle : xs.length ≤ (List.finRange n).length :=
    nodup_length_le_of_subset h (fun x _ => List.mem_finRange x)
  simpa [List.length_finRange] using hle
