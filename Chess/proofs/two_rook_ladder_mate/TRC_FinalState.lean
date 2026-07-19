import ChessRules
import TRC_FunctionWithInvariant
import LadderStepIsLegal
import TRC_Invariant_BlackEmpty
import TRC_Invariant_CheckLocations

-- ============================================================
-- FINAL LADDER STATE
-- ============================================================
-- A "final" ladder state is the unique configuration from which White's
-- next ply checkmates Black. In our system this is phase = moveRa with
-- rank.val + 3 = n (so rookA after applyLadderStep sits at (n-1, 0),
-- pinning the Black king on rank n-1 with no escape).

def IsFinalLadderState {n : Nat} (s : LadderState n) : Prop :=
  s.phase = .moveRa ∧ s.rank.val + 3 = n

instance {n : Nat} (s : LadderState n) : Decidable (IsFinalLadderState s) := by
  unfold IsFinalLadderState; infer_instance

-- After applyLadderStep on a final state, the Black king is in check
-- from rookA, which has just moved to (rank+2, 0) = (n-1, 0). The Black
-- king is forced to rank n-1 by the LadderShape invariants
-- (rank > rookAPos.rank = rank+1 plus rank < n; with rank+3 = n the
-- only legal Black-king rank is n-1).
lemma LadderStep_IsCheck_AtFinal {n : Nat} (s : LadderState n)
    (h_final : IsFinalLadderState s) :
    IsCheck (applyLadderStep s.shape) .Black := by
  obtain ⟨board, rank, phase, shape⟩ := s
  obtain ⟨h_phase, h_rank⟩ := h_final
  subst h_phase
  -- The step board is a legal setup, so it has a (unique) black king.
  obtain ⟨_, _, _, _, h_step_legal⟩ := ladderStep_isLegal shape
  obtain ⟨_, ⟨kp, hkp, _⟩, _⟩ := h_step_legal
  -- That king has file ≥ 2 and rank strictly above the pre-move rookA
  -- rank (= rank + 1). With rank + 3 = n and kp.rank < n, its rank is
  -- pinned to rank + 2 — exactly one above the pre-move rookA.
  obtain ⟨hfile, hrank⟩ := LadderMove_BlackKing_FarFromRa shape kp hkp
  refine LadderMove_BlackInCheck_AtRaRankPlusOne_FileGe2_moveRa
    shape kp hkp ?_ hfile
  have hRa : (rookAPos rank .moveRa shape.hRfits).rank.val = rank.val + 1 := rfl
  have hn : rank.val + 3 = n := h_rank
  have hlt := kp.rank.isLt
  omega

-- After applyLadderStep on a final state, the Black king has no legal
-- destination: ranks n-2 and n-1 are covered by the two rooks, files 0
-- and 1 are covered, and rank n is off-board. Stated in the form the
-- second conjunct of IsCheckmate uses (kingMoveTargets).
lemma LadderStep_NoKingEscape_AtFinal {n : Nat} (s : LadderState n)
    (h_final : IsFinalLadderState s) :
    ∀ src,
      (applyLadderStep s.shape) src = some ⟨.Black, .King⟩ →
      ∀ dst ∈ kingMoveTargets (applyLadderStep s.shape) src .Black,
        IsCheck (applyMove (applyLadderStep s.shape) src dst) .Black := by
  sorry

-- Black has no rook (LadderShape's only-Black-King clause), so the
-- rook part of IsCheckmate is vacuous.
lemma LadderStep_NoBlackRook {n : Nat} (s : LadderState n) :
    ∀ src, (applyLadderStep s.shape) src ≠ some ⟨.Black, .Rook⟩ := by
  intro src h_rook
  exact PieceType.noConfusion
    (LadderMove_PreservesOnlyBlackKing s.shape src .Rook h_rook)

-- Combining the three: applyLadderStep on a final state delivers checkmate.
theorem IsCheckmate_AtFinal {n : Nat} (s : LadderState n)
    (h_final : IsFinalLadderState s) :
    IsCheckmate (applyLadderStep s.shape) .Black := by
  refine ⟨LadderStep_IsCheck_AtFinal s h_final, fun src => ⟨?_, ?_⟩⟩
  · exact LadderStep_NoKingEscape_AtFinal s h_final src
  · intro h_rook
    exact absurd h_rook (LadderStep_NoBlackRook s src)
