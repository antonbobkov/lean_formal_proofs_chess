import HelloWorld.Chess

-- ============================================================
-- Tests for the mini-chess module
-- ============================================================
-- `#guard expr` evaluates `expr` at build time.
-- If it returns `false`, the build fails with an error.
-- This gives us compile-time assertions — no test runner needed.


-- ------------------------------------------------------------
-- BOARD BUILDER
-- ------------------------------------------------------------
-- A helper to construct a Board from a list of (square, piece) pairs.
-- Any square not in the list is empty (returns `none`).
--
-- `List.find?` scans the list for a matching square.
-- `.map (·.2)` transforms `Option (Pos × Piece)` into `Option Piece`
-- by extracting the second element of the pair.
-- The `·` is shorthand for a lambda: `fun x => x.2`.
def boardFrom (squares : List (Pos 4 × Piece)) : Board 4 :=
  fun p => (squares.find? fun (q, _) => q == p).map (·.2)


-- ------------------------------------------------------------
-- PIECE SHORTHANDS
-- ------------------------------------------------------------
-- `private` means these names are only visible in this file.
private def WK : Piece := ⟨.White, .King⟩  -- White King
private def WR : Piece := ⟨.White, .Rook⟩  -- White Rook
private def BK : Piece := ⟨.Black, .King⟩  -- Black King
private def BR : Piece := ⟨.Black, .Rook⟩  -- Black Rook

-- Square shorthand: takes a row and column as `Fin 4` literals.
-- Numeric literals like `0`, `3` are automatically elaborated as
-- `Fin 4` because that's the declared parameter type.
private def sq (r c : Fin 4) : Pos 4 := (r, c)


-- ============================================================
-- ROOK CHECK TESTS
-- ============================================================

-- Board layout (WK=White King, BR=Black Rook, . =empty):
--   col  0  1  2  3
-- row 0 [WK  .  .  BR]
-- row 1 [ .  .  .   .]
-- row 2 [ .  .  .   .]
-- row 3 [ .  .  .   .]
-- The rook and king are on the same row with nothing between them → CHECK.
#guard IsCheck (boardFrom [(sq 0 0, WK), (sq 0 3, BR)]) .White

-- Same idea but vertically (same column):
--   col  0  1  2  3
-- row 0 [WK  .  .   .]
-- row 1 [ .  .  .   .]
-- row 2 [ .  .  .   .]
-- row 3 [BR  .  .   .]
-- Rook slides up the column, no blockers → CHECK.
#guard IsCheck (boardFrom [(sq 0 0, WK), (sq 3 0, BR)]) .White

-- A piece between the rook and king blocks the attack:
--   col  0  1  2  3
-- row 0 [WK WR  .  BR]
-- The white rook at (0,1) sits between king (0,0) and black rook (0,3).
-- The black rook's line of sight is blocked → NOT in check.
#guard ¬ IsCheck (boardFrom [(sq 0 0, WK), (sq 0 1, WR), (sq 0 3, BR)]) .White

-- Rook on a completely different row AND column — can't attack diagonally:
--   col  0  1  2  3
-- row 0 [WK  .  .   .]
-- row 1 [ .  .  .  BR]
#guard ¬ IsCheck (boardFrom [(sq 0 0, WK), (sq 1 3, BR)]) .White

-- Rook immediately adjacent (no squares between them) → still CHECK.
-- `Between 1 2 x` is false for all x (no integer strictly between 1 and 2),
-- so nothing can block, and the attack succeeds.
#guard IsCheck (boardFrom [(sq 1 1, WK), (sq 1 2, BR)]) .White

-- A friendly (same-color) rook does NOT give check:
#guard ¬ IsCheck (boardFrom [(sq 0 0, WK), (sq 0 3, WR)]) .White


-- ============================================================
-- KING CHECK TESTS
-- ============================================================

-- Adjacent black king → white king in check (kings threaten their neighbors):
--   col  0  1
-- row 0 [WK BK]
#guard IsCheck (boardFrom [(sq 0 0, WK), (sq 0 1, BK)]) .White

-- Diagonal adjacency also counts:
--   col  0  1
-- row 0 [WK  .]
-- row 1 [ .  BK]
#guard IsCheck (boardFrom [(sq 0 0, WK), (sq 1 1, BK)]) .White

-- Kings two squares apart — out of range:
#guard ¬ IsCheck (boardFrom [(sq 0 0, WK), (sq 0 2, BK)]) .White

-- Kings far apart:
#guard ¬ IsCheck (boardFrom [(sq 0 0, WK), (sq 2 3, BK)]) .White


-- ============================================================
-- EDGE CASES
-- ============================================================

-- No king of the asked color on the board → false (defensive total behavior):
#guard ¬ IsCheck (boardFrom [(sq 0 3, BR)]) .White

-- Kings in corners, black rook gives check to black king (friendly fire is
-- impossible — we're asking about White's king here, which doesn't exist):
#guard ¬ IsCheck (boardFrom [(sq 3 3, BK), (sq 0 3, BR)]) .White

-- Black king in check by a white rook:
--   col  0  1  2  3
-- row 0 [BK  .  .  WK]
-- row 3 [WR  .  .   .]
-- White rook at (3,0) attacks black king at (0,0) along column 0 → CHECK.
#guard IsCheck (boardFrom [(sq 0 0, BK), (sq 0 3, WK), (sq 3 0, WR)]) .Black

-- The same board is NOT check for White (white king is safe):
#guard ¬ IsCheck (boardFrom [(sq 0 0, BK), (sq 0 3, WK), (sq 3 0, WR)]) .White


-- ============================================================
-- LEGAL SETUP TESTS
-- ============================================================

-- One king each, well separated → legal.
#guard IsLegalSetup (boardFrom [(sq 0 0, WK), (sq 3 3, BK)])

-- Kings adjacent horizontally → illegal (touching).
#guard ¬ IsLegalSetup (boardFrom [(sq 0 0, WK), (sq 0 1, BK)])

-- Kings adjacent diagonally → also illegal.
#guard ¬ IsLegalSetup (boardFrom [(sq 0 0, WK), (sq 1 1, BK)])

-- Missing black king → illegal.
#guard ¬ IsLegalSetup (boardFrom [(sq 0 0, WK)])

-- Missing white king → illegal.
#guard ¬ IsLegalSetup (boardFrom [(sq 3 3, BK)])

-- Two white kings → illegal.
#guard ¬ IsLegalSetup (boardFrom [(sq 0 0, WK), (sq 2 0, WK), (sq 3 3, BK)])

-- Empty board → illegal.
#guard ¬ IsLegalSetup (boardFrom ([] : List (Pos 4 × Piece)))


-- ============================================================
-- CHECKMATE TESTS
-- ============================================================

-- Three-rook mate: two rooks seal column 0 and the diagonal; a third
-- checks along row 0.  BK has three candidate squares:
--   (0,1) — attacked by WR at (0,3) along row 0
--   (1,0) — BK captures WR there, but WR at (2,0) immediately gives check
--   (1,1) — attacked by WR at (1,0) along row 1
-- col  0  1  2  3
-- row 0 [BK  .  .  WR]
-- row 1 [WR  .  .   .]
-- row 2 [WR  .  .   .]
-- row 3 [ .  .  WK  .]
#guard IsCheckmate (boardFrom [(sq 0 0, BK), (sq 0 3, WR), (sq 1 0, WR), (sq 2 0, WR), (sq 3 2, WK)]) .Black

-- White is not in checkmate on the same board (white king is never in check):
#guard ¬ IsCheckmate (boardFrom [(sq 0 0, BK), (sq 0 3, WR), (sq 1 0, WR), (sq 2 0, WR), (sq 3 2, WK)]) .White

-- In check but can escape: BK moves to (1,0) which nothing attacks.
#guard ¬ IsCheckmate (boardFrom [(sq 0 0, BK), (sq 0 3, WR), (sq 3 3, WK)]) .Black

-- Not in check → cannot be checkmate.
#guard ¬ IsCheckmate (boardFrom [(sq 0 0, BK), (sq 3 3, WK)]) .Black

-- In check but BK can capture the attacker: after BK takes WR at (1,0),
-- the white king at (3,3) is too far to threaten (1,0).
#guard ¬ IsCheckmate (boardFrom [(sq 0 0, BK), (sq 1 0, WR), (sq 3 3, WK)]) .Black

-- In check, king cannot escape, but a friendly rook can interpose:
-- BK at (0,0) is checked by WR at (0,3); WR at (1,3) covers all of
-- row 1 so BK has nowhere to run, but BR at (2,1) can slide to (0,1)
-- and block the check along row 0.
#guard ¬ IsCheckmate (boardFrom [(sq 0 0, BK), (sq 0 3, WR), (sq 1 3, WR), (sq 3 0, WK), (sq 2 1, BR)]) .Black
