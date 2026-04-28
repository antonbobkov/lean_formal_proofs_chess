import ChessRules
import FunctionDefinition

-- ============================================================
-- SANITY TESTS for Two-Rook Ladder Mate
-- ============================================================
-- Build a concrete 8×8 board for each phase and check the move
-- function returns the expected (src, dst) pair.

private def WK : Piece := ⟨.White, .King⟩
private def WR : Piece := ⟨.White, .Rook⟩
private def BK : Piece := ⟨.Black, .King⟩

-- Position shorthand for n=8 — `Fin 8` literals elaborate from numerals.
private def sq8 (r c : Fin 8) : Pos 8 := (r, c)

-- A board with White {K@(0,0), R_b@(0,1), R_a@(1,0)} and Black {K@(3,3)}.
-- Phase = moveRb: about to move b-file rook up.
private def boardRb : Board 8 where
  pieces p :=
    if p = sq8 0 0 then some WK
    else if p = sq8 0 1 then some WR
    else if p = sq8 1 0 then some WR
    else if p = sq8 3 3 then some BK
    else none
  turn := .White

-- After move 1: R_b moved (0,1) → (1,1). Phase = moveRa.
private def boardRa : Board 8 where
  pieces p :=
    if p = sq8 0 0 then some WK
    else if p = sq8 1 1 then some WR
    else if p = sq8 1 0 then some WR
    else if p = sq8 3 3 then some BK
    else none
  turn := .White

-- After move 2: R_a moved (1,0) → (2,0). Phase = moveK.
private def boardK : Board 8 where
  pieces p :=
    if p = sq8 0 0 then some WK
    else if p = sq8 1 1 then some WR
    else if p = sq8 2 0 then some WR
    else if p = sq8 3 3 then some BK
    else none
  turn := .White

-- After move 3: K moved (0,0) → (1,0). Same shape with R = 1, phase = moveRb.
private def boardRbShifted : Board 8 where
  pieces p :=
    if p = sq8 1 0 then some WK
    else if p = sq8 1 1 then some WR
    else if p = sq8 2 0 then some WR
    else if p = sq8 3 3 then some BK
    else none
  turn := .White


-- The four boards each match their declared `LadderShape`.
#guard decide (LadderShape boardRb         (0 : Fin 8) .moveRb)
#guard decide (LadderShape boardRa         (0 : Fin 8) .moveRa)
#guard decide (LadderShape boardK          (0 : Fin 8) .moveK)
#guard decide (LadderShape boardRbShifted  (1 : Fin 8) .moveRb)


-- The move function returns the expected (src, dst) for each phase.
#guard nextWhiteMove (rank := (0 : Fin 8)) (φ := .moveRb)
        (by decide : LadderShape boardRb (0 : Fin 8) .moveRb)
       == (sq8 0 1, sq8 1 1)

#guard nextWhiteMove (rank := (0 : Fin 8)) (φ := .moveRa)
        (by decide : LadderShape boardRa (0 : Fin 8) .moveRa)
       == (sq8 1 0, sq8 2 0)

#guard nextWhiteMove (rank := (0 : Fin 8)) (φ := .moveK)
        (by decide : LadderShape boardK (0 : Fin 8) .moveK)
       == (sq8 0 0, sq8 1 0)


-- Three plies starting from `boardRb` reach `boardRbShifted`.
private def afterCycle : Board 8 :=
  let b1 := ladderStep (board := boardRb) (rank := (0 : Fin 8)) (φ := .moveRb)
              (by decide)
  -- Black "passes" by recording a non-move; but `applyMove` flips turn,
  -- so we manually flip the turn back to White to feed the next ladder
  -- step. (Real play interleaves a Black move; for this cycle-shape
  -- check we use the all-White trajectory and only inspect piece
  -- positions, not turns.)
  let b1w : Board 8 := { b1 with turn := .White }
  let b2 := ladderStep (board := b1w) (rank := (0 : Fin 8)) (φ := .moveRa)
              (by decide)
  let b2w : Board 8 := { b2 with turn := .White }
  let b3 := ladderStep (board := b2w) (rank := (0 : Fin 8)) (φ := .moveK)
              (by decide)
  b3

-- After three White plies (with manual turn-resets), every square
-- matches `boardRbShifted` (modulo the final turn flip — both have
-- White to move on `boardRbShifted` but `afterCycle` has Black to
-- move because the last `applyMove` flipped it).
#guard ∀ p ∈ allPositions 8, afterCycle.pieces p == boardRbShifted.pieces p
