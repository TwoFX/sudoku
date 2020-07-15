/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import widget

open sudoku

theorem easy1 (s : sudoku) (c01 : s.f (0, 1) = 7) (c04 : s.f (0, 4) = 2) (c05 : s.f (0, 5) = 6) (c06 : s.f (0, 6) = 5) (c11 : s.f (1, 1) = 4) (c13 : s.f (1, 3) = 9) (c16 : s.f (1, 6) = 7) (c17 : s.f (1, 7) = 8) (c20 : s.f (2, 0) = 2) (c22 : s.f (2, 2) = 8) (c23 : s.f (2, 3) = 4) (c27 : s.f (2, 7) = 9) (c32 : s.f (3, 2) = 1) (c35 : s.f (3, 5) = 3) (c36 : s.f (3, 6) = 9) (c37 : s.f (3, 7) = 4) (c40 : s.f (4, 0) = 6) (c42 : s.f (4, 2) = 5) (c43 : s.f (4, 3) = 1) (c44 : s.f (4, 4) = 7) (c51 : s.f (5, 1) = 3) (c56 : s.f (5, 6) = 1) (c58 : s.f (5, 8) = 7) (c60 : s.f (6, 0) = 5) (c64 : s.f (6, 4) = 9) (c66 : s.f (6, 6) = 4) (c67 : s.f (6, 7) = 3) (c71 : s.f (7, 1) = 2) (c72 : s.f (7, 2) = 4) (c74 : s.f (7, 4) = 5) (c75 : s.f (7, 5) = 8) (c83 : s.f (8, 3) = 7) (c87 : s.f (8, 7) = 5) (c88 : s.f (8, 8) = 9) : s.f (0, 0) = 3 ∧ s.f (0, 1) = 7 ∧ s.f (0, 2) = 9 ∧ s.f (0, 3) = 8 ∧ s.f (0, 4) = 2 ∧ s.f (0, 5) = 6 ∧ s.f (0, 6) = 5 ∧ s.f (0, 7) = 1 ∧ s.f (0, 8) = 4 ∧ s.f (1, 0) = 1 ∧ s.f (1, 1) = 4 ∧ s.f (1, 2) = 6 ∧ s.f (1, 3) = 9 ∧ s.f (1, 4) = 3 ∧ s.f (1, 5) = 5 ∧ s.f (1, 6) = 7 ∧ s.f (1, 7) = 8 ∧ s.f (1, 8) = 2 ∧ s.f (2, 0) = 2 ∧ s.f (2, 1) = 5 ∧ s.f (2, 2) = 8 ∧ s.f (2, 3) = 4 ∧ s.f (2, 4) = 1 ∧ s.f (2, 5) = 7 ∧ s.f (2, 6) = 3 ∧ s.f (2, 7) = 9 ∧ s.f (2, 8) = 6 ∧ s.f (3, 0) = 7 ∧ s.f (3, 1) = 8 ∧ s.f (3, 2) = 1 ∧ s.f (3, 3) = 2 ∧ s.f (3, 4) = 6 ∧ s.f (3, 5) = 3 ∧ s.f (3, 6) = 9 ∧ s.f (3, 7) = 4 ∧ s.f (3, 8) = 5 ∧ s.f (4, 0) = 6 ∧ s.f (4, 1) = 9 ∧ s.f (4, 2) = 5 ∧ s.f (4, 3) = 1 ∧ s.f (4, 4) = 7 ∧ s.f (4, 5) = 4 ∧ s.f (4, 6) = 8 ∧ s.f (4, 7) = 2 ∧ s.f (4, 8) = 3 ∧ s.f (5, 0) = 4 ∧ s.f (5, 1) = 3 ∧ s.f (5, 2) = 2 ∧ s.f (5, 3) = 5 ∧ s.f (5, 4) = 8 ∧ s.f (5, 6) = 1 ∧ s.f (5, 7) = 6 ∧ s.f (5, 8) = 7 ∧ s.f (6, 0) = 5 ∧ s.f (6, 1) = 1 ∧ s.f (6, 2) = 7 ∧ s.f (6, 3) = 6 ∧ s.f (6, 4) = 9 ∧ s.f (6, 5) = 2 ∧ s.f (6, 6) = 4 ∧ s.f (6, 7) = 3 ∧ s.f (6, 8) = 8 ∧ s.f (7, 0) = 9 ∧ s.f (7, 1) = 2 ∧ s.f (7, 2) = 4 ∧ s.f (7, 3) = 3 ∧ s.f (7, 4) = 5 ∧ s.f (7, 5) = 8 ∧ s.f (7, 6) = 6 ∧ s.f (7, 7) = 7 ∧ s.f (7, 8) = 1 ∧ s.f (8, 0) = 8 ∧ s.f (8, 1) = 6 ∧ s.f (8, 2) = 3 ∧ s.f (8, 3) = 7 ∧ s.f (8, 4) = 4 ∧ s.f (8, 5) = 1 ∧ s.f (8, 6) = 2 ∧ s.f (8, 7) = 5 ∧ s.f (8, 8) = 9 :=
begin [show_sudoku]
  have c77 : s.f (7, 7) = 7 := by box_logic,
  have c06 : s.f (0, 7) = 1 := by col_logic,
  have c30 : s.f (3, 0) = 7 := by box_logic,
  have c62 : s.f (6, 2) = 7 := by box_logic,
  have c50 : s.f (5, 0) = 4 := by box_logic,
  have c45 : s.f (4, 5) = 4 := by box_logic,
  have c84 : s.f (8, 4) = 4 := by box_logic,
  have c70 : s.f (7, 0) = 9 := by box_logic,
  have c02 : s.f (0, 2) = 9 := by row_logic,
  have c21 : s.f (2, 1) = 5 := by box_logic,
  have c10 : s.f (1, 0) = 1 := by box_logic,
  have c00 : s.f (0, 0) = 3 := by naked_single,
  have c80 : s.f (8, 0) = 8 := by naked_single,
  have c12 : s.f (1, 2) = 6 := by naked_single,
  have c08 : s.f (0, 8) = 4 := by row_logic,
  have c03 : s.f (0, 3) = 8 := by row_logic,
  have c68 : s.f (6, 8) = 8 := by box_logic,
  have c78 : s.f (7, 8) = 1 := by box_logic,
  have c86 : s.f (8, 6) = 2 := by box_logic,
  have c76 : s.f (7, 6) = 6 := by box_logic,
  have c73 : s.f (7, 3) = 3 := by box_logic,
  have c82 : s.f (8, 2) = 3 := by row_logic,
  have c63 : s.f (6, 3) = 6 := by box_logic,
  have c65 : s.f (6, 5) = 2 := by box_logic,
  have c85 : s.f (8, 5) = 1 := by box_logic,
  have c81 : s.f (8, 1) = 6 := by row_logic,
  have c61 : s.f (6, 1) = 1 := by box_logic,
  have c62 : s.f (6, 2) = 7 := by box_logic,
  have c46 : s.f (4, 6) = 8 := by col_logic,
  have c26 : s.f (2, 6) = 3 := by col_logic,
  have c18 : s.f (1, 8) = 2 := by box_logic,
  have c28 : s.f (2, 8) = 6 := by box_logic,
  have c48 : s.f (4, 8) = 3 := by col_logic,
  have c38 : s.f (3, 8) = 5 := by col_logic,
  have c47 : s.f (4, 7) = 2 := by row_logic,
  have c57 : s.f (5, 7) = 6 := by col_logic,
  have c24 : s.f (2, 4) = 1 := by box_logic,
  have c14 : s.f (1, 4) = 3 := by box_logic,
  have c15 : s.f (1, 5) = 5 := by box_logic,
  have c25 : s.f (2, 5) = 7 := by box_logic,
  have c52 : s.f (5, 2) = 2 := by col_logic,
  have c41 : s.f (4, 1) = 9 := by row_logic,
  have c31 : s.f (3, 1) = 8 := by col_logic,
  have c33 : s.f (3, 3) = 2 := by row_logic,
  have c34 : s.f (3, 4) = 6 := by row_logic,
  have c53 : s.f (5, 3) = 5 := by col_logic,
  have c54 : s.f (5, 4) = 8 := by col_logic,
  have c55 : s.f (5, 5) = 9 := by col_logic,
  repeat { all_goals { split <|> assumption } },
end

#print easy1
