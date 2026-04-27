import ChessRules
import BasicProofs

-- ============================================================
-- PROOF: Checkmate is impossible with only two kings
-- ============================================================
-- Strategy:
--   1. From a legal setup, extract unique positions for both kings.
--      `IsLegalSetup.kings_not_adjacent` (from BasicProofs) gives us
--      that the two kings do not attack each other.
--   2. With only kings on the board (only_kings_on_board), the only
--      possible attacker against a king is the opponent king.
--   3. By KingAttacks symmetry + non-adjacency, no attack is possible.
--   4. So the king is not in check, hence not in checkmate.


-- Every occupied square contains a king (of either color).
def only_kings_on_board {n : Nat} (b : Board n) : Prop :=
  ∀ p piece, b p = some piece → piece.kind = .King


theorem not_check_implies_not_checkmate {n : Nat} (b : Board n) (c : Color) :
    ¬IsCheck b c → ¬IsCheckmate b c :=
  fun h ⟨hc, _⟩ => h hc


-- ============================================================
-- MAIN THEOREM: Checkmate impossible with only two kings
-- ============================================================
theorem checkmate_impossible_two_kings {n : Nat} (b : Board n)
    (hlegal : IsLegalSetup b) (hokings : only_kings_on_board b) :
    ∀ c, ¬IsCheckmate b c := by
  -- Extract the kings-not-adjacent fact before `obtain` destructures `hlegal`.
  have hno_attack := IsLegalSetup.kings_not_adjacent hlegal
  -- ∃! unfolds to ⟨witness, membership, uniqueness function⟩
  obtain ⟨⟨pos_w, hwhite, huniq_w⟩, ⟨pos_b, hblack, huniq_b⟩, _⟩ := hlegal
  intro c
  apply not_check_implies_not_checkmate
  intro h_check
  obtain ⟨kpos, hk, p, hcase⟩ := h_check
  rcases hcase with ⟨hbp, _⟩ | ⟨hbp, hattack⟩
  · -- Attacker would be a Rook, but only_kings_on_board says otherwise.
    cases hokings p _ hbp
  · -- Attacker is the opponent king; ∃! pins each position uniquely.
    cases c
    · -- White king: kpos = pos_w, opponent p = pos_b; attack reverses via symmetry.
      rw [huniq_w kpos hk, huniq_b p hbp] at hattack
      exact hno_attack pos_w pos_b hwhite hblack ((KingAttacks_comm _ _).mp hattack)
    · -- Black king: kpos = pos_b, opponent p = pos_w; attack direction matches.
      rw [huniq_b kpos hk, huniq_w p hbp] at hattack
      exact hno_attack pos_w pos_b hwhite hblack hattack
