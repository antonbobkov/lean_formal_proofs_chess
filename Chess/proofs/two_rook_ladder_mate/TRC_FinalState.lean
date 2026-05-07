import ChessRules
import TRC_FunctionWithInvariant
import LadderStepIsLegal

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
  sorry

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
  sorry

-- Combining the three: applyLadderStep on a final state delivers checkmate.
theorem IsCheckmate_AtFinal {n : Nat} (s : LadderState n)
    (h_final : IsFinalLadderState s) :
    IsCheckmate (applyLadderStep s.shape) .Black := by
  sorry
