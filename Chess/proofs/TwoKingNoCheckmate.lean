import ChessRules

-- ============================================================
-- PROOF: Checkmate is impossible with only two kings
-- ============================================================
-- Strategy:
--   1. From a legal setup, extract unique positions for both kings,
--      together with the fact that the two kings do not attack each other.
--   2. With only kings on the board (only_kings_on_board), the only
--      possible attacker against a king is the opponent king.
--   3. By KingAttacks symmetry + non-adjacency, no attack is possible.
--   4. So the king is not in check, hence not in checkmate.


-- Every occupied square contains a king (of either color).
def only_kings_on_board {n : Nat} (b : Board n) : Prop :=
  ∀ p piece, b p = some piece → piece.kind = .King


theorem WithinOne_comm (a b : Nat) : WithinOne a b ↔ WithinOne b a := by
  unfold WithinOne
  rw [Nat.max_comm, Nat.min_comm]


theorem KingAttacks_comm {n : Nat} (a b : Pos n) :
    KingAttacks a b ↔ KingAttacks b a := by
  unfold KingAttacks
  rw [WithinOne_comm a.1.val b.1.val, WithinOne_comm a.2.val b.2.val]
  exact ⟨fun ⟨h, x, y⟩ => ⟨h.symm, x, y⟩, fun ⟨h, x, y⟩ => ⟨h.symm, x, y⟩⟩


theorem not_check_implies_not_checkmate {n : Nat} (b : Board n) (c : Color) :
    ¬IsCheck b c → ¬IsCheckmate b c :=
  fun h ⟨hc, _⟩ => h hc


-- ============================================================
-- MAIN THEOREM: Checkmate impossible with only two kings
-- ============================================================
theorem checkmate_impossible_two_kings {n : Nat} (b : Board n)
    (hlegal : IsLegalSetup b) (hokings : only_kings_on_board b) :
    ∀ c, ¬IsCheckmate b c := by
  intro c
  obtain ⟨pos_w, pos_b, hwhite_uniq, hblack_uniq, hno_attack⟩ := hlegal
  -- Pick the defending king pos_c and attacker king pos_o per color.
  -- KingAttacks is symmetric, so the no-attack fact transfers either way.
  obtain ⟨pos_c, pos_o, hc_uniq, ho_uniq, hno_attack_oc⟩ :
      ∃ pos_c pos_o,
        (∀ p, b p = some ⟨c, .King⟩ ↔ p = pos_c) ∧
        (∀ p, b p = some ⟨c.opponent, .King⟩ ↔ p = pos_o) ∧
        ¬ KingAttacks pos_o pos_c := by
    cases c
    · exact ⟨pos_w, pos_b, hwhite_uniq, hblack_uniq,
             fun h => hno_attack ((KingAttacks_comm _ _).mp h)⟩
    · exact ⟨pos_b, pos_w, hblack_uniq, hwhite_uniq, hno_attack⟩
  apply not_check_implies_not_checkmate
  intro h_check
  obtain ⟨kpos, hk, p, hcase⟩ := h_check
  rcases hcase with ⟨hbp, _⟩ | ⟨hbp, hattack⟩
  · -- Attacker would be a Rook, but only_kings_on_board says otherwise.
    cases hokings p _ hbp
  · -- Attacker is the opponent king; uniqueness pins p = pos_o, kpos = pos_c.
    have hkpos : kpos = pos_c := (hc_uniq kpos).mp hk
    have hp : p = pos_o := (ho_uniq p).mp hbp
    rw [hkpos, hp] at hattack
    exact hno_attack_oc hattack
