import SquareGame.Cert6
import SquareGame.Cert7
import SquareGame.Cert8
import SquareGame.Cert9
import SquareGame.Cert10
import SquareGame.Cert11
import SquareGame.Cert12
import SquareGame.Cert13
import SquareGame.Cert14

/-!
# The result

The nine board sizes whose outcome was open: `n = 6 … 14`.  Below them, Jenrich
settled `n ≤ 5` in 2012; above them, no square-free two-colouring of the 15 × 15
grid exists (Bacher–Eliahou 2010), so the game cannot be drawn and strategy
stealing rules out a second-player win.
-/

namespace SquareGame

/-- **The first player wins the square achievement game on every board that was
open**, forcing a square of their own within 15 plies. -/
theorem first_player_wins_open_cases :
    Forces (squares 6) 36 15 0 0 ∧ Forces (squares 7) 49 15 0 0 ∧
    Forces (squares 8) 64 15 0 0 ∧ Forces (squares 9) 81 15 0 0 ∧
    Forces (squares 10) 100 15 0 0 ∧ Forces (squares 11) 121 15 0 0 ∧
    Forces (squares 12) 144 15 0 0 ∧ Forces (squares 13) 169 15 0 0 ∧
    Forces (squares 14) 196 15 0 0 :=
  ⟨first_player_wins_6, first_player_wins_7, first_player_wins_8,
   first_player_wins_9, first_player_wins_10, first_player_wins_11,
   first_player_wins_12, first_player_wins_13, first_player_wins_14⟩

end SquareGame
