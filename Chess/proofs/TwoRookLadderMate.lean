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

def kingPos {n : Nat} (R : Fin n) (h : R.val + 2 < n) : Pos n :=
  (R, ⟨0, by omega⟩)

def rookBPos {n : Nat} (R : Fin n) (φ : LadderPhase) (h : R.val + 2 < n) : Pos n :=
  match φ with
  | .moveRb => (R, ⟨1, by omega⟩)
  | .moveRa => (⟨R.val + 1, by omega⟩, ⟨1, by omega⟩)
  | .moveK  => (⟨R.val + 1, by omega⟩, ⟨1, by omega⟩)

def rookAPos {n : Nat} (R : Fin n) (φ : LadderPhase) (h : R.val + 2 < n) : Pos n :=
  match φ with
  | .moveRb => (⟨R.val + 1, by omega⟩, ⟨0, by omega⟩)
  | .moveRa => (⟨R.val + 1, by omega⟩, ⟨0, by omega⟩)
  | .moveK  => (⟨R.val + 2, by omega⟩, ⟨0, by omega⟩)


-- ------------------------------------------------------------
-- INVARIANT
-- ------------------------------------------------------------
-- We use `dite` so the bound `R.val + 2 < n` is *part of* the
-- proposition: `LadderShape` reduces to `False` when the bound
-- fails, and to a plain conjunction when it holds. This keeps the
-- shape decidable without needing a hand-written instance.
def LadderShape {n : Nat} (b : Board n) (R : Fin n) (φ : LadderPhase) : Prop :=
  if h : R.val + 2 < n then
    b.turn = .White ∧
    b (kingPos R h) = some ⟨.White, .King⟩ ∧
    b (rookBPos R φ h) = some ⟨.White, .Rook⟩ ∧
    b (rookAPos R φ h) = some ⟨.White, .Rook⟩ ∧
    (∀ p, (b p = some ⟨.White, .King⟩ ∨ b p = some ⟨.White, .Rook⟩) →
          p = kingPos R h ∨ p = rookBPos R φ h ∨ p = rookAPos R φ h) ∧
    (∃! bp, b bp = some ⟨.Black, .King⟩) ∧
    (∀ p, b p ≠ some ⟨.Black, .Rook⟩) ∧
    IsLegalSetup b
  else False

instance {n : Nat} (b : Board n) (R : Fin n) (φ : LadderPhase) :
    Decidable (LadderShape b R φ) := by
  unfold LadderShape ExistsUnique; infer_instance


-- ------------------------------------------------------------
-- BOUND-EXTRACTION LEMMA
-- ------------------------------------------------------------
-- `LadderShape` carries the bound `R.val + 2 < n` implicitly: if
-- the bound fails, the proposition reduces to `False`. This lemma
-- pulls the bound out so we can hand it to the move function.
theorem LadderShape.hRfits {n : Nat} {b : Board n} {R : Fin n} {φ : LadderPhase}
    (h : LadderShape b R φ) : R.val + 2 < n := by
  unfold LadderShape at h
  by_cases hbnd : R.val + 2 < n
  · exact hbnd
  · rw [dif_neg hbnd] at h; exact h.elim


-- ------------------------------------------------------------
-- THE NEXT WHITE MOVE
-- ------------------------------------------------------------
-- Given a `LadderShape` proof, return the (src, dst) pair for
-- the unique White move dictated by the procedure. Total — the
-- proof guarantees the bound holds.
def nextWhiteMove {n : Nat} {b : Board n} {R : Fin n} {φ : LadderPhase}
    (h : LadderShape b R φ) : Pos n × Pos n :=
  have hbnd : R.val + 2 < n := h.hRfits
  match φ with
  | .moveRb => (rookBPos R .moveRb hbnd, rookBPos R .moveRa hbnd)
  | .moveRa => (rookAPos R .moveRa hbnd, rookAPos R .moveK  hbnd)
  | .moveK  => (kingPos  R hbnd, (⟨R.val + 1, by omega⟩, ⟨0, by omega⟩))


-- ------------------------------------------------------------
-- APPLY THE NEXT WHITE MOVE
-- ------------------------------------------------------------
-- Returns the board after one White ply. `applyMove` already flips
-- the turn, so the resulting board has Black to move.
def ladderStep {n : Nat} {b : Board n} {R : Fin n} {φ : LadderPhase}
    (h : LadderShape b R φ) : Board n :=
  let move := nextWhiteMove h
  applyMove b move.1 move.2


-- ------------------------------------------------------------
-- PHASE ADVANCEMENT (informational)
-- ------------------------------------------------------------
-- After one White ply, the next phase is given by `nextPhase`.
-- The base rank advances (R → R+1) only after `moveK`.
def nextPhase : LadderPhase → LadderPhase
  | .moveRb => .moveRa
  | .moveRa => .moveK
  | .moveK  => .moveRb


-- ============================================================
-- SANITY TESTS
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
#guard nextWhiteMove (R := (0 : Fin 8)) (φ := .moveRb)
        (by decide : LadderShape boardRb (0 : Fin 8) .moveRb)
       == (sq8 0 1, sq8 1 1)

#guard nextWhiteMove (R := (0 : Fin 8)) (φ := .moveRa)
        (by decide : LadderShape boardRa (0 : Fin 8) .moveRa)
       == (sq8 1 0, sq8 2 0)

#guard nextWhiteMove (R := (0 : Fin 8)) (φ := .moveK)
        (by decide : LadderShape boardK (0 : Fin 8) .moveK)
       == (sq8 0 0, sq8 1 0)


-- Three plies starting from `boardRb` reach `boardRbShifted`.
private def afterCycle : Board 8 :=
  let b1 := ladderStep (b := boardRb) (R := (0 : Fin 8)) (φ := .moveRb)
              (by decide)
  -- Black "passes" by recording a non-move; but `applyMove` flips turn,
  -- so we manually flip the turn back to White to feed the next ladder
  -- step. (Real play interleaves a Black move; for this cycle-shape
  -- check we use the all-White trajectory and only inspect piece
  -- positions, not turns.)
  let b1w : Board 8 := { b1 with turn := .White }
  let b2 := ladderStep (b := b1w) (R := (0 : Fin 8)) (φ := .moveRa)
              (by decide)
  let b2w : Board 8 := { b2 with turn := .White }
  let b3 := ladderStep (b := b2w) (R := (0 : Fin 8)) (φ := .moveK)
              (by decide)
  b3

-- After three White plies (with manual turn-resets), every square
-- matches `boardRbShifted` (modulo the final turn flip — both have
-- White to move on `boardRbShifted` but `afterCycle` has Black to
-- move because the last `applyMove` flipped it).
#guard ∀ p ∈ allPositions 8, afterCycle.pieces p == boardRbShifted.pieces p
