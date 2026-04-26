import HelloWorld.Chess
import HelloWorld.FinLemma

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


-- ============================================================
-- PROOF: Checkmate is impossible with only two kings
-- ============================================================
-- Strategy:
--   1. From a legal setup, extract unique positions for both kings,
--      together with the fact that the two kings do not attack each other.
--   2. With only kings on the board (only_kings_on_board), the only
--      possible attacker against a king is the opponent king.
--   3. By kingAttacks symmetry + non-adjacency, no attack is possible.
--   4. So the king is not in check, hence not in checkmate.


-- Every occupied square contains a king (of either color).
def only_kings_on_board {n : Nat} (b : Board n) : Prop :=
  ∀ p piece, b p = some piece → piece.kind = .King


-- ============================================================
-- HELPER: every position is in allPositions
-- ============================================================
theorem mem_allPositions {n : Nat} (p : Pos n) : p ∈ allPositions n := by
  obtain ⟨r, c⟩ := p
  unfold allPositions
  rw [List.mem_flatMap]
  refine ⟨r, List.mem_finRange r, ?_⟩
  rw [List.mem_map]
  exact ⟨c, List.mem_finRange c, rfl⟩


-- ============================================================
-- HELPER: withinOne is symmetric
-- ============================================================
private theorem withinOne_symm (a b : Nat) : withinOne a b = withinOne b a := by
  unfold withinOne
  rw [Nat.max_comm, Nat.min_comm]


-- ============================================================
-- HELPER: kingAttacks is symmetric
-- ============================================================
theorem kingAttacks_symm {n : Nat} (a b : Pos n) :
    kingAttacks a b = kingAttacks b a := by
  unfold kingAttacks
  by_cases h : a = b
  · subst h; rfl
  · have hne : (a == b) = false := by simp [h]
    have hne' : (b == a) = false := by simp [Ne.symm h]
    rw [hne, hne']
    obtain ⟨sr, sc⟩ := a
    obtain ⟨tr, tc⟩ := b
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [withinOne_symm sr.val tr.val, withinOne_symm sc.val tc.val]


-- ============================================================
-- LEMMA: legal setup gives unique kings of each color
-- ============================================================
theorem legal_setup_has_both_kings {n : Nat} {b : Board n}
    (hlegals : isLegalSetup b = true) :
    ∃ pos_w pos_b,
      (∀ p, b p = some ⟨.White, .King⟩ ↔ p = pos_w) ∧
      (∀ p, b p = some ⟨.Black, .King⟩ ↔ p = pos_b) ∧
      kingAttacks pos_w pos_b = false := by
  unfold isLegalSetup at hlegals
  rcases h_w : (allPositions n).filter (fun p => b p == some ⟨.White, .King⟩)
    with _ | ⟨wp, _ | ⟨_, _⟩⟩
  · rw [h_w] at hlegals; simp at hlegals
  · rcases h_b : (allPositions n).filter (fun p => b p == some ⟨.Black, .King⟩)
      with _ | ⟨bp, _ | ⟨_, _⟩⟩
    · rw [h_w, h_b] at hlegals; simp at hlegals
    · refine ⟨wp, bp, ?_, ?_, ?_⟩
      · intro p
        constructor
        · intro hp
          have hp_in :
              p ∈ (allPositions n).filter (fun q => b q == some ⟨.White, .King⟩) := by
            rw [List.mem_filter]
            exact ⟨mem_allPositions p, by simp [hp]⟩
          rw [h_w] at hp_in
          simpa using hp_in
        · intro h_eq
          rw [h_eq]
          have hwp_in :
              wp ∈ (allPositions n).filter (fun q => b q == some ⟨.White, .King⟩) := by
            rw [h_w]; exact List.mem_singleton.mpr rfl
          rw [List.mem_filter] at hwp_in
          simpa using hwp_in.2
      · intro p
        constructor
        · intro hp
          have hp_in :
              p ∈ (allPositions n).filter (fun q => b q == some ⟨.Black, .King⟩) := by
            rw [List.mem_filter]
            exact ⟨mem_allPositions p, by simp [hp]⟩
          rw [h_b] at hp_in
          simpa using hp_in
        · intro h_eq
          rw [h_eq]
          have hbp_in :
              bp ∈ (allPositions n).filter (fun q => b q == some ⟨.Black, .King⟩) := by
            rw [h_b]; exact List.mem_singleton.mpr rfl
          rw [List.mem_filter] at hbp_in
          simpa using hbp_in.2
      · rw [h_w, h_b] at hlegals; simp at hlegals; exact hlegals
    · rw [h_w, h_b] at hlegals; simp at hlegals
  · rw [h_w] at hlegals; simp at hlegals


-- ============================================================
-- HELPER: find? returns `some x` when x is the unique match
-- ============================================================
private theorem find?_eq_some_of_mem_unique {α : Type} {p : α → Bool} {l : List α} {x : α}
    (hmem : x ∈ l) (hpx : p x = true)
    (huniq : ∀ y ∈ l, p y = true → y = x) :
    l.find? p = some x := by
  induction l with
  | nil => simp at hmem
  | cons a rest ih =>
    by_cases hpa : p a = true
    · have ha_eq : a = x := huniq a (List.mem_cons.mpr (.inl rfl)) hpa
      subst ha_eq
      simp [hpa]
    · have hpaF : p a = false := by
        cases h : p a with
        | true => exact absurd h hpa
        | false => rfl
      have hxrest : x ∈ rest := by
        rcases List.mem_cons.mp hmem with heq | hin
        · subst heq; rw [hpx] at hpaF; exact Bool.noConfusion hpaF
        · exact hin
      have huniq_rest : ∀ y ∈ rest, p y = true → y = x := fun y hy hpy =>
        huniq y (List.mem_cons.mpr (.inr hy)) hpy
      simp [hpaF, ih hxrest huniq_rest]


-- ============================================================
-- LEMMA: findKing returns the unique king position
-- ============================================================
theorem findKing_eq_of_unique {n : Nat} {b : Board n} {c : Color} {pos : Pos n}
    (h : ∀ p, b p = some ⟨c, .King⟩ ↔ p = pos) :
    findKing b c = some pos := by
  unfold findKing
  apply find?_eq_some_of_mem_unique (mem_allPositions pos)
  · simp [(h pos).mpr rfl]
  · intro q _ hq
    exact (h q).mp (by simpa using hq)


-- ============================================================
-- LEMMA: Not in check implies not in checkmate
-- ============================================================
theorem not_check_implies_not_checkmate {n : Nat} (b : Board n) (c : Color) :
    ¬isCheck b c → ¬isCheckmate b c := by
  intro h_not_check
  unfold isCheckmate
  simp [h_not_check]


-- ============================================================
-- MAIN THEOREM: Checkmate impossible with only two kings
-- ============================================================
theorem checkmate_impossible_two_kings {n : Nat} (b : Board n)
    (hlegals : isLegalSetup b) (hokings : only_kings_on_board b) :
    ∀ c, ¬isCheckmate b c := by
  intro c
  obtain ⟨pos_w, pos_b, hwhite_uniq, hblack_uniq, hno_attack⟩ :=
    legal_setup_has_both_kings hlegals
  -- Pick the defending king `pos_c` and opponent king `pos_o` per color.
  -- `kingAttacks` is symmetric, so the no-attack fact transfers either way.
  obtain ⟨pos_c, pos_o, hc_uniq, ho_uniq, hno_attack_oc⟩ :
      ∃ pos_c pos_o,
        (∀ p, b p = some ⟨c, .King⟩ ↔ p = pos_c) ∧
        (∀ p, b p = some ⟨c.opponent, .King⟩ ↔ p = pos_o) ∧
        kingAttacks pos_o pos_c = false := by
    cases c
    · exact ⟨pos_w, pos_b, hwhite_uniq, hblack_uniq, kingAttacks_symm _ _ ▸ hno_attack⟩
    · exact ⟨pos_b, pos_w, hblack_uniq, hwhite_uniq, hno_attack⟩
  apply not_check_implies_not_checkmate
  intro h_check
  unfold isCheck at h_check
  rw [findKing_eq_of_unique hc_uniq] at h_check
  rw [List.any_eq_true] at h_check
  obtain ⟨p, _, hp_pred⟩ := h_check
  match h_bp : b p with
  | none =>
    rw [h_bp] at hp_pred
    simp at hp_pred
  | some piece =>
    rw [h_bp] at hp_pred
    by_cases h_color : piece.color = c.opponent
    · -- Opponent piece. By only_kings_on_board, it must be a king.
      have h_kind : piece.kind = .King := hokings p piece h_bp
      have h_piece_eq : piece = ⟨c.opponent, .King⟩ := by
        cases piece with
        | mk pc pk =>
          simp only at h_color h_kind
          subst h_color; subst h_kind; rfl
      have hp_eq_o : p = pos_o := (ho_uniq p).mp (by rw [h_bp, h_piece_eq])
      rw [h_piece_eq, hp_eq_o] at hp_pred
      simp [hno_attack_oc] at hp_pred
    · simp [h_color] at hp_pred
