import ChessRules
import TRC_FunctionWithInvariant
import TRC_Invariant_Preservation

-- ------------------------------------------------------------
-- TERMINATION / CHECKMATE THEOREM (statement only)
-- ------------------------------------------------------------
-- The ladder forces checkmate for Black in finitely many full cycles
-- (one White ply + one legal Black ply each), regardless of how Black
-- plays.
--
-- `reply` is an arbitrary Black strategy: given the board after the
-- White ply it picks (src, dst).  `hreply` witnesses that every chosen
-- move is legal.  The iteration uses `Function.iterate` (^[k]) on the
-- one-cycle step that advances the LadderState via
-- `LadderShape.preservation`.
theorem ladderMate_termination {n : Nat}
    (s₀    : LadderState n)
    (reply  : (b : Board n) → Pos n × Pos n)
    (hreply : ∀ s : LadderState n,
        IsLegalMove (applyLadderStep s.shape)
                    (reply (applyLadderStep s.shape)).1
                    (reply (applyLadderStep s.shape)).2) :
    ∃ k : Nat,
      IsCheckmate
        ((fun s : LadderState n =>
            { board := applyMove (applyLadderStep s.shape)
                         (reply (applyLadderStep s.shape)).1
                         (reply (applyLadderStep s.shape)).2
              rank  := nextRank s.rank s.phase s.shape.hRfits
              phase := nextPhase s.phase
              -- TODO: restructure `step` to skip the boundary moveK case
              -- (where `s.rank.val + 3 < n` fails); at that boundary Black
              -- is already checkmated so preservation is not needed.
              shape := LadderShape.preservation s.shape sorry (hreply s) })^[k] s₀).board
        .Black := by
  sorry
