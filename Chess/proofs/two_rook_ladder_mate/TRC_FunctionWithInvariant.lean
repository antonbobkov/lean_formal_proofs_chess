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
  ⟨rank, ⟨0, by omega⟩⟩

def rookBPos {n : Nat} (rank : Fin n) (φ : LadderPhase)
    (space_left : rank.val + 2 < n) : Pos n :=
  match φ with
  | .moveRb => ⟨rank, ⟨1, by omega⟩⟩
  | .moveRa => ⟨⟨rank.val + 1, by omega⟩, ⟨1, by omega⟩⟩
  | .moveK  => ⟨⟨rank.val + 1, by omega⟩, ⟨1, by omega⟩⟩

def rookAPos {n : Nat} (rank : Fin n) (φ : LadderPhase)
    (space_left : rank.val + 2 < n) : Pos n :=
  match φ with
  | .moveRb => ⟨⟨rank.val + 1, by omega⟩, ⟨0, by omega⟩⟩
  | .moveRa => ⟨⟨rank.val + 1, by omega⟩, ⟨0, by omega⟩⟩
  | .moveK  => ⟨⟨rank.val + 2, by omega⟩, ⟨0, by omega⟩⟩


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
    let K  := kingPos  rank   space_left
    let Rb := rookBPos rank φ space_left
    let Ra := rookAPos rank φ space_left
    board.turn = .White ∧
    board K  = some ⟨.White, .King⟩ ∧
    board Rb = some ⟨.White, .Rook⟩ ∧
    board Ra = some ⟨.White, .Rook⟩ ∧
    (∀ p, (∃ k, board p = some ⟨.White, k⟩) →
          p = K ∨ p = Rb ∨ p = Ra) ∧
    (∀ bp, board bp = some ⟨.Black, .King⟩ → Ra.rank < bp.rank) ∧
    (∀ p k, board p = some ⟨.Black, k⟩ → k = .King) ∧
    IsLegalSetup board
  else False

instance {n : Nat} (board : Board n) (rank : Fin n) (φ : LadderPhase) :
    Decidable (LadderShape board rank φ) := by
  unfold LadderShape; infer_instance


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
-- UNFOLDING LEMMA
-- ------------------------------------------------------------
-- Extracts the conjunction inside `LadderShape` (which is wrapped in
-- a `dite` on the `space_left` bound).
lemma LadderShape.unfold {n : Nat} {board : Board n} {rank : Fin n}
    {φ : LadderPhase} (lsh : LadderShape board rank φ) :
    let h := lsh.hRfits
    board.turn = .White ∧
    board (kingPos rank h) = some ⟨.White, .King⟩ ∧
    board (rookBPos rank φ h) = some ⟨.White, .Rook⟩ ∧
    board (rookAPos rank φ h) = some ⟨.White, .Rook⟩ ∧
    (∀ p, (∃ k, board p = some ⟨.White, k⟩) →
          p = kingPos rank h ∨
          p = rookBPos rank φ h ∨
          p = rookAPos rank φ h) ∧
    (∀ bp, board bp = some ⟨.Black, .King⟩ →
           (rookAPos rank φ h).rank < bp.rank) ∧
    (∀ p k, board p = some ⟨.Black, k⟩ → k = .King) ∧
    IsLegalSetup board := by
  have hbnd := lsh.hRfits
  have h := lsh
  unfold LadderShape at h
  rw [dif_pos hbnd] at h
  exact h


-- ------------------------------------------------------------
-- THE NEXT WHITE MOVE
-- ------------------------------------------------------------
-- Given a `LadderShape` proof, return the (src, dst) pair for
-- the unique White move dictated by the procedure. Total — the
-- proof guarantees the bound holds.
def ladderStep {n : Nat} {board : Board n} {rank : Fin n} {φ : LadderPhase}
    (ladder_shape_hypothesis : LadderShape board rank φ) : Pos n × Pos n :=
  have hbnd : rank.val + 2 < n := ladder_shape_hypothesis.hRfits
  match φ with
  | .moveRb => (rookBPos rank .moveRb hbnd, rookBPos rank .moveRa hbnd)
  | .moveRa => (rookAPos rank .moveRa hbnd, rookAPos rank .moveK  hbnd)
  | .moveK  =>
      (kingPos rank hbnd, ⟨⟨rank.val + 1, by omega⟩, ⟨0, by omega⟩⟩)


-- ------------------------------------------------------------
-- APPLY THE NEXT WHITE MOVE
-- ------------------------------------------------------------
-- Returns the board after one White ply. `applyMove` already flips
-- the turn, so the resulting board has Black to move.
def applyLadderStep {n : Nat} {board : Board n} {rank : Fin n} {φ : LadderPhase}
    (ladder_shape_hypothesis : LadderShape board rank φ) : Board n :=
  let move := ladderStep ladder_shape_hypothesis
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
-- LADDER STATE
-- ------------------------------------------------------------
-- Bundles the board with its invariant proof so that the
-- one-cycle step function has type `LadderState n → LadderState n`
-- and can be iterated with `^[k]`.
structure LadderState (n : Nat) where
  board : Board n
  rank  : Fin n
  phase : LadderPhase
  shape : LadderShape board rank phase
