import ChessRules
import TRC_FunctionWithInvariant
import NextWhiteMoveIsLegal

-- ------------------------------------------------------------
-- WHITE-PIECE POSITIONS AFTER ONE LADDER PLY
-- ------------------------------------------------------------
-- After white's ladder ply, the three white pieces sit at specific
-- squares — namely the squares predicted by the *next* `LadderShape`
-- state's position helpers (`nextRank` for rank, `nextPhase` for the
-- rook configuration). Two pieces are unchanged (proved via
-- `NoCaptureMove_PreservesPiece`); the third is at the move's `dst`.
-- The moveK case additionally needs the next-rank bound
-- `rank.val + 3 < n` to form `kingPos` / `rookXPos` for `rank+1`.

-- Phase moveRb: white moves Rb (rank,1) → (rank+1,1).
-- Resulting positions match `LadderShape` for (rank, .moveRa).
lemma applyLadderStep_PiecesAt_moveRb {n : Nat} {board : Board n} {rank : Fin n}
    (lsh : LadderShape board rank .moveRb) :
    let h := lsh.hRfits
    let b' := applyLadderStep lsh
    b' (kingPos rank h) = some ⟨.White, .King⟩ ∧
    b' (rookBPos rank .moveRa h) = some ⟨.White, .Rook⟩ ∧
    b' (rookAPos rank .moveRa h) = some ⟨.White, .Rook⟩ := by
  obtain ⟨_, hK_at, hRb_at, hRa_at, _⟩ := lsh.unfold
  have dst_empty := LadderMove_IntoEmptySquare lsh
  have h_src_eq : (ladderStep lsh).1 = rookBPos rank .moveRb lsh.hRfits := rfl
  refine ⟨?_, ?_, ?_⟩
  · -- King unchanged at (rank, 0)
    apply NoCaptureMove_PreservesPiece _ _ _ _ _ hK_at _ dst_empty
    rw [h_src_eq]; intro heq
    have := congrArg (fun p : Pos n => p.file.val) heq
    simp [kingPos, rookBPos] at this
  · -- Rb moved to (rank+1, 1) = dst
    show (applyMove board _ (rookBPos rank .moveRa lsh.hRfits)).pieces _ = _
    unfold applyMove; simp; rw [h_src_eq]; exact hRb_at
  · -- Ra unchanged at (rank+1, 0)
    apply NoCaptureMove_PreservesPiece _ _ _ _ _ hRa_at _ dst_empty
    rw [h_src_eq]; intro heq
    have := congrArg (fun p : Pos n => p.file.val) heq
    simp [rookBPos, rookAPos] at this

-- Phase moveRa: white moves Ra (rank+1,0) → (rank+2,0).
-- Resulting positions match `LadderShape` for (rank, .moveK).
lemma applyLadderStep_PiecesAt_moveRa {n : Nat} {board : Board n} {rank : Fin n}
    (lsh : LadderShape board rank .moveRa) :
    let h := lsh.hRfits
    let b' := applyLadderStep lsh
    b' (kingPos rank h) = some ⟨.White, .King⟩ ∧
    b' (rookBPos rank .moveK h) = some ⟨.White, .Rook⟩ ∧
    b' (rookAPos rank .moveK h) = some ⟨.White, .Rook⟩ := by
  obtain ⟨_, hK_at, hRb_at, hRa_at, _⟩ := lsh.unfold
  have dst_empty := LadderMove_IntoEmptySquare lsh
  have h_src_eq : (ladderStep lsh).1 = rookAPos rank .moveRa lsh.hRfits := rfl
  refine ⟨?_, ?_, ?_⟩
  · -- King unchanged at (rank, 0)
    apply NoCaptureMove_PreservesPiece _ _ _ _ _ hK_at _ dst_empty
    rw [h_src_eq]; intro heq
    have := congrArg (fun p : Pos n => p.rank.val) heq
    simp [kingPos, rookAPos] at this
  · -- Rb unchanged at (rank+1, 1)
    apply NoCaptureMove_PreservesPiece _ _ _ _ _ hRb_at _ dst_empty
    rw [h_src_eq]; intro heq
    have := congrArg (fun p : Pos n => p.file.val) heq
    simp [rookBPos, rookAPos] at this
  · -- Ra moved to (rank+2, 0) = dst
    show (applyMove board _ (rookAPos rank .moveK lsh.hRfits)).pieces _ = _
    unfold applyMove; simp; rw [h_src_eq]; exact hRa_at

-- Phase moveK: white moves K (rank,0) → (rank+1,0).
-- Resulting positions match `LadderShape` for (rank+1, .moveRb), i.e.
-- the next state's position helpers — paralleling moveRb/moveRa above.
-- This requires the next-rank bound `rank.val + 3 < n`.
lemma applyLadderStep_PiecesAt_moveK {n : Nat} {board : Board n} {rank : Fin n}
    (lsh : LadderShape board rank .moveK)
    (hRoom : rank.val + 3 < n) :
    let rank' : Fin n := ⟨rank.val + 1, by omega⟩
    let h' : rank'.val + 2 < n := hRoom
    let b' := applyLadderStep lsh
    b' (kingPos rank' h') = some ⟨.White, .King⟩ ∧
    b' (rookBPos rank' .moveRb h') = some ⟨.White, .Rook⟩ ∧
    b' (rookAPos rank' .moveRb h') = some ⟨.White, .Rook⟩ := by
  obtain ⟨_, hK_at, hRb_at, hRa_at, _⟩ := lsh.unfold
  have dst_empty := LadderMove_IntoEmptySquare lsh
  have h_src_eq : (ladderStep lsh).1 = kingPos rank lsh.hRfits := rfl
  refine ⟨?_, ?_, ?_⟩
  · -- King moved to dst; rewrite the target square as `(ladderStep lsh).2`
    -- (defeq to `kingPos rank' h'` modulo proof irrelevance) so the `==` in
    -- `applyMove` reduces.
    show (applyMove board (ladderStep lsh).1 (ladderStep lsh).2).pieces
        (ladderStep lsh).2 = some ⟨.White, .King⟩
    unfold applyMove; simp; rw [h_src_eq]; exact hK_at
  · -- Rb unchanged at (rank+1, 1) = rookBPos (rank+1) .moveRb _
    apply NoCaptureMove_PreservesPiece _ _ _ _ _ hRb_at _ dst_empty
    rw [h_src_eq]; intro heq
    have := congrArg (fun p : Pos n => p.file.val) heq
    simp [kingPos, rookBPos] at this
  · -- Ra unchanged at (rank+2, 0) = rookAPos (rank+1) .moveRb _
    apply NoCaptureMove_PreservesPiece _ _ _ _ _ hRa_at _ dst_empty
    rw [h_src_eq]; intro heq
    have := congrArg (fun p : Pos n => p.rank.val) heq
    simp [kingPos, rookAPos] at this
