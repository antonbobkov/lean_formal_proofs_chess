import ChessRules

-- ============================================================
-- Two-Rook Deterministic Ladder Mate
-- ============================================================
-- White has King + two Rooks ("a-file" and "b-file"); Black has only
-- a King. Every cycle of three White plies shifts the white setup up
-- by one rank.
--
-- Invariant (start of cycle, parameterised by base rank R : Fin n):
--   K = (R, 0),  R_b = (R, 1),  R_a = (R+1, 0),  White to move.
--
-- The three plies of a cycle:
--   1. .moveRb : R_b moves up — (R,1) → (R+1,1)
--   2. .moveRa : R_a moves up — (R+1,0) → (R+2,0)
--   3. .moveK  : K moves up   — (R,0) → (R+1,0)
--
-- After the cycle, the setup matches the invariant for R' = R+1.
-- This file formalises the invariant and the deterministic move
-- function consumed via a `LadderShape` proof; preservation and
-- eventual-checkmate theorems are out of scope.


-- ------------------------------------------------------------
-- PHASE TAG
-- ------------------------------------------------------------
inductive LadderPhase
  | moveRb
  | moveRa
  | moveK
  deriving DecidableEq, Repr


-- ------------------------------------------------------------
-- WHITE PIECE POSITIONS (parameterised by base rank R and phase)
-- ------------------------------------------------------------
-- The bound `R.val + 2 < n` is needed because the procedure refers
-- to ranks R, R+1, and R+2; without it some target squares would
-- not exist on the board.
--
-- Mapping:
--   φ        K           R_b          R_a
--   moveRb   (R, 0)      (R, 1)       (R+1, 0)
--   moveRa   (R, 0)      (R+1, 1)     (R+1, 0)
--   moveK    (R, 0)      (R+1, 1)     (R+2, 0)

def kingPos {n : Nat} (rank : Fin n)
    (space_left : rank.val + 2 < n) : Pos n :=
  (rank, ⟨0, by omega⟩)

def rookBPos {n : Nat} (rank : Fin n) (φ : LadderPhase)
    (space_left : rank.val + 2 < n) : Pos n :=
  match φ with
  | .moveRb => (rank, ⟨1, by omega⟩)
  | .moveRa => (⟨rank.val + 1, by omega⟩, ⟨1, by omega⟩)
  | .moveK  => (⟨rank.val + 1, by omega⟩, ⟨1, by omega⟩)

def rookAPos {n : Nat} (rank : Fin n) (φ : LadderPhase)
    (space_left : rank.val + 2 < n) : Pos n :=
  match φ with
  | .moveRb => (⟨rank.val + 1, by omega⟩, ⟨0, by omega⟩)
  | .moveRa => (⟨rank.val + 1, by omega⟩, ⟨0, by omega⟩)
  | .moveK  => (⟨rank.val + 2, by omega⟩, ⟨0, by omega⟩)


-- ------------------------------------------------------------
-- INVARIANT
-- ------------------------------------------------------------
-- We use `dite` so the bound `R.val + 2 < n` is *part of* the
-- proposition: `LadderShape` reduces to `False` when the bound
-- fails, and to a plain conjunction when it holds. This keeps the
-- shape decidable without needing a hand-written instance.
def LadderShape {n : Nat} (board : Board n) (rank : Fin n)
    (φ : LadderPhase) : Prop :=
  if space_left : rank.val + 2 < n then
    board.turn = .White ∧
    board (kingPos rank space_left) = some ⟨.White, .King⟩ ∧
    board (rookBPos rank φ space_left) =
        some ⟨.White, .Rook⟩ ∧
    board (rookAPos rank φ space_left) =
        some ⟨.White, .Rook⟩ ∧
    (∀ p, (board p = some ⟨.White, .King⟩ ∨
           board p = some ⟨.White, .Rook⟩) →
          p = kingPos rank space_left ∨
          p = rookBPos rank φ space_left ∨
          p = rookAPos rank φ space_left) ∧
    (∃! bp, board bp = some ⟨.Black, .King⟩) ∧
    (∀ bp, board bp = some ⟨.Black, .King⟩ →
           (rookAPos rank φ space_left).1 < bp.1) ∧
    (∀ p k, board p = some ⟨.Black, k⟩ → k = .King) ∧
    IsLegalSetup board
  else False

instance {n : Nat} (board : Board n) (rank : Fin n) (φ : LadderPhase) :
    Decidable (LadderShape board rank φ) := by
  unfold LadderShape ExistsUnique; infer_instance


-- ------------------------------------------------------------
-- BOUND-EXTRACTION LEMMA
-- ------------------------------------------------------------
-- `LadderShape` carries the bound `R.val + 2 < n` implicitly: if
-- the bound fails, the proposition reduces to `False`. This lemma
-- pulls the bound out so we can hand it to the move function.
theorem LadderShape.hRfits {n : Nat} {board : Board n} {rank : Fin n}
    {φ : LadderPhase}
    (ladder_shape_hypothesis : LadderShape board rank φ) :
    rank.val + 2 < n := by
  unfold LadderShape at ladder_shape_hypothesis
  by_cases hbnd : rank.val + 2 < n
  · exact hbnd
  · rw [dif_neg hbnd] at ladder_shape_hypothesis
    exact ladder_shape_hypothesis.elim


-- ------------------------------------------------------------
-- THE NEXT WHITE MOVE
-- ------------------------------------------------------------
-- Given a `LadderShape` proof, return the (src, dst) pair for
-- the unique White move dictated by the procedure. Total — the
-- proof guarantees the bound holds.
def nextWhiteMove {n : Nat} {board : Board n} {rank : Fin n} {φ : LadderPhase}
    (ladder_shape_hypothesis : LadderShape board rank φ) : Pos n × Pos n :=
  have hbnd : rank.val + 2 < n := ladder_shape_hypothesis.hRfits
  match φ with
  | .moveRb => (rookBPos rank .moveRb hbnd, rookBPos rank .moveRa hbnd)
  | .moveRa => (rookAPos rank .moveRa hbnd, rookAPos rank .moveK  hbnd)
  | .moveK  =>
      (kingPos rank hbnd, (⟨rank.val + 1, by omega⟩, ⟨0, by omega⟩))

-- The move selected by the ladder procedure is always legal.
theorem nextWhiteMove_isLegal {n : Nat} {board : Board n}
    {rank : Fin n} {φ : LadderPhase}
    (lsh : LadderShape board rank φ) :
    IsLegalMove board
      (nextWhiteMove lsh).1 (nextWhiteMove lsh).2 := by
  sorry
  -- ----------------------------------------------------------------
  -- PROOF SKETCH
  -- ----------------------------------------------------------------
  -- `IsLegalMove board src dst` expands to two conjuncts:
  --   A. The piece at src belongs to the side to move (White) and its
  --      geometry is valid (rook: clear line; king: one-step).
  --   B. `IsLegalSetup (applyMove board src dst)`, which itself splits:
  --      B1. Exactly one White King exists on the new board.
  --      B2. Exactly one Black King exists on the new board.
  --      B3. `¬ IsCheck b' .White`  (b'.turn = Black after applyMove,
  --          so b'.turn.opponent = White; i.e., White was not left in
  --          check by its own move).
  --
  -- We proceed by case analysis on `φ`.  In each case we first unfold
  -- `LadderShape` to obtain named hypotheses:
  --   ht       : board.turn = .White
  --   hK       : board (kingPos rank hbnd) = some ⟨.White, .King⟩
  --   hRb      : board (rookBPos rank φ hbnd) = some ⟨.White, .Rook⟩
  --   hRa      : board (rookAPos rank φ hbnd) = some ⟨.White, .Rook⟩
  --   huniq    : all squares with a White piece are K, Rb, Ra
  --   hbk      : ∃! bp, board bp = some ⟨.Black, .King⟩
  --   hbk_above: ∀ bp, board bp = some ⟨.Black, .King⟩ →
  --                rookAPos.1 < bp.1          -- Black King above rookA's rank
  --   honly_k  : ∀ p k, board p = some ⟨.Black, k⟩ → k = .King
  --   hsetup   : IsLegalSetup board
  --              (which includes ¬ IsCheck board .Black, because it is
  --               White's turn and the invariant forbids the opponent
  --               to be in check at the start of a move)
  --
  -- ── Case φ = moveRb ─────────────────────────────────────────────
  -- src = (rank, 1)   dst = (rank+1, 1)   (Rook B moves one rank up)
  --
  -- Goal A (right disjunct): board src = some ⟨.White, .Rook⟩  by hRb.
  --   ValidRookMove: src and dst share column 1; they are adjacent
  --   ranks, so no square lies strictly *between* them → path clear. ✓
  --   (Rewrite board.turn via ht.)
  --
  -- Goal B1: White King is still uniquely at (rank, 0) — untouched. ✓
  --
  -- Goal B2: dst = (rank+1, 1) was empty before the move (no capture):
  --   • Not a White piece: huniq places all White pieces at K, Rb, Ra,
  --     none of which equals (rank+1, 1) in phase moveRb.
  --   • Not the Black King: hbk_above gives rookAPos.1 = rank+1 < bp.1,
  --     so the Black King is strictly above rank+1 and cannot be at
  --     rank+1. ✓
  --   Since no piece was at dst, the Black King is still unique. ✓
  --
  -- Goal B3: After the move, b'.turn = Black.  White King is at
  --   (rank, 0).  The only Black piece is the Black King, at some row
  --   > rank+1.  Row difference from rank is ≥ 2 > 1, so the Black
  --   King is not adjacent to the White King → no check. ✓
  --
  -- ── Case φ = moveRa ─────────────────────────────────────────────
  -- src = (rank+1, 0)   dst = (rank+2, 0)   (Rook A moves one rank up)
  --
  -- Goal A: board src = some ⟨.White, .Rook⟩  by hRa.
  --   ValidRookMove: same column (col 0), adjacent ranks → path clear. ✓
  --
  -- Goal B2 (the interesting part): dst = (rank+2, 0) was empty:
  --   • Not a White piece: huniq (K at (rank,0), Rb at (rank+1,1),
  --     Ra at (rank+1,0) — none equals (rank+2,0)). ✓
  --   • Not the Black King: suppose for contradiction the Black King is
  --     at (rank+2, 0).  Then the White Rook Ra at (rank+1, 0) attacks
  --     it along col 0 with no intervening piece (adjacent ranks).
  --     That means IsCheck board .Black holds.  But hsetup contains
  --     ¬ IsCheck board .Black (White to move, opponent = Black).
  --     Contradiction. ✓
  --
  -- Goals B1, B3: same argument as moveRb case. ✓
  --
  -- ── Case φ = moveK ──────────────────────────────────────────────
  -- src = (rank, 0)   dst = (rank+1, 0)   (King steps one rank up)
  -- In phase moveK the pieces are: K=(rank,0), Rb=(rank+1,1), Ra=(rank+2,0).
  --
  -- Goal A (left disjunct): board src = some ⟨.White, .King⟩  by hK.
  --   ValidKingMove: src ≠ dst (different rows), WithinOne rank (rank+1)
  --   (differ by 1) ✓, WithinOne 0 0 (same column, differ by 0) ✓.
  --
  -- dst = (rank+1, 0) was empty before the king moves there:
  --   • Not Rb (that's at (rank+1, 1), different column). ✓
  --   • Not Ra (that's at (rank+2, 0), different rank). ✓
  --   • Not the Black King: hbk_above gives Ra.1 = rank+2 < bp.1, so
  --     the Black King is strictly above rank+2 and cannot be at
  --     rank+1. ✓
  --   No capture occurs; all three White pieces and the Black King
  --   survive — uniqueness is preserved.
  --
  -- Goal B1: White King is now uniquely at (rank+1, 0). ✓
  -- Goal B2: Black King unchanged (no capture). ✓
  --
  -- Goal B3: After the move, White King at (rank+1, 0).  Black King
  --   is at some row > rank+2, so row difference from rank+1 is ≥ 2.
  --   The Black King cannot attack the White King. ✓
  -- ----------------------------------------------------------------


-- ------------------------------------------------------------
-- APPLY THE NEXT WHITE MOVE
-- ------------------------------------------------------------
-- Returns the board after one White ply. `applyMove` already flips
-- the turn, so the resulting board has Black to move.
def ladderStep {n : Nat} {board : Board n} {rank : Fin n} {φ : LadderPhase}
    (ladder_shape_hypothesis : LadderShape board rank φ) : Board n :=
  let move := nextWhiteMove ladder_shape_hypothesis
  applyMove board move.1 move.2


-- ------------------------------------------------------------
-- PHASE ADVANCEMENT (informational)
-- ------------------------------------------------------------
-- After one White ply, the next phase is given by `nextPhase`.
-- The base rank advances (R → R+1) only after `moveK`.
def nextPhase : LadderPhase → LadderPhase
  | .moveRb => .moveRa
  | .moveRa => .moveK
  | .moveK  => .moveRb


-- ------------------------------------------------------------
-- RANK ADVANCEMENT
-- ------------------------------------------------------------
-- The base rank advances only on the moveK ply; the other two
-- plies keep the same rank.
def nextRank {n : Nat} (rank : Fin n) (φ : LadderPhase)
    (space_left : rank.val + 2 < n) : Fin n :=
  match φ with
  | .moveK => ⟨rank.val + 1, by omega⟩
  | _      => rank


-- ------------------------------------------------------------
-- PRESERVATION THEOREM (statement only)
-- ------------------------------------------------------------
-- After one White ply (ladderStep) and any legal Black reply,
-- the resulting board satisfies LadderShape for the advanced
-- rank and the next phase.
theorem LadderShape.preservation {n : Nat} {board : Board n}
    {rank : Fin n} {φ : LadderPhase}
    (lsh : LadderShape board rank φ)
    {bsrc bdst : Pos n}
    (black_move : IsLegalMove (ladderStep lsh) bsrc bdst) :
    LadderShape
      (applyMove (ladderStep lsh) bsrc bdst)
      (nextRank rank φ lsh.hRfits)
      (nextPhase φ) := by
  sorry


-- **Termination / checkmate theorem**: to be stated later.
-- `∃ k, IsCheckmate ((step ∘ blackReply)^[k] b) .Black`.
