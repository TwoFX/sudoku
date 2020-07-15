/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import basic

universes u v w

open tactic

def list.mfirst' {m : Type → Type v} [monad m] {α : Type} [inhabited α] (f : α → m bool) : list α → m α
| [] := return $ default _
| (a::as) := do
  r ← f a,
  if r then return a else list.mfirst' as

def list.mfiltermap {m : Type u → Type v} [monad m] {α : Type w} {β : Type u}
  (f : α → m (option β)) : list α → m (list β)
| [] := return []
| (x::xs) := do
    y ← f x,
    r ← list.mfiltermap xs,
    match y with
    | none := return r
    | some z := return (z::r)
    end

namespace tactic.sudoku

meta def get_sudoku : tactic expr :=
local_context >>= list.mfirst' (λ t, (do `(sudoku) ← infer_type t, return tt) <|> return ff)

def indices : list (fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]
def numbers : list (fin 9) := [1, 2, 3, 4, 5, 6, 7, 8, 9]

meta structure cell_data :=
(row col val : fin 9)
(e : expr)

meta instance format_cell_data : has_to_format cell_data :=
{ to_format := λ d,
  format!"{cell_data.e d}" }

meta def parse_cell_data (s e : expr) : tactic (option cell_data) :=
(do
  `(sudoku.f %%s (%%a, %%b) = %%c) ← infer_type e,
  u ← eval_expr (fin 9) a,
  v ← eval_expr (fin 9) b,
  w ← eval_expr (fin 9) c,
  return $ some ⟨u, v, w, e⟩) <|> return none

meta def get_cell_data (s : expr) : tactic (list cell_data) :=
local_context >>= list.mfiltermap (parse_cell_data s)

meta def mk_row_conflict (s : expr) (l r : cell_data) : tactic unit :=
do
  guard (l.row = r.row),
  guard (l.val = r.val),
  guard (l.col ≠ r.col),
  to_expr ``(sudoku.row_conflict %%s %%l.e %%r.e dec_trivial) >>= exact

meta def mk_col_conflict (s : expr) (l r : cell_data) : tactic unit :=
do
  guard (l.row ≠ r.row),
  guard (l.val = r.val),
  guard (l.col = r.col),
  to_expr ``(sudoku.col_conflict %%s %%l.e %%r.e dec_trivial) >>= exact

meta def mk_cell_conflict (s : expr) (l r : cell_data) : tactic unit :=
do
  guard (l.row = r.row),
  guard (l.col = r.col),
  guard (l.val ≠ r.val),
  to_expr ``(sudoku.cell_conflict %%s %%l.e %%r.e dec_trivial) >>= exact

meta def mk_box_conflict (s : expr) (l r : cell_data) : tactic unit :=
do
  guard (l.val = r.val),
  guard (l.row / 3 = r.row / 3),
  guard (l.col / 3 = r.col / 3),
  guard (l.row ≠ r.row ∨ l.col ≠ r.col),
  to_expr ``(sudoku.box_conflict %%s %%l.e %%r.e dec_trivial dec_trivial dec_trivial) >>= exact

meta def loop (cd : list cell_data) (f : cell_data → cell_data → tactic unit) : tactic unit :=
list.mfirst (λ l : cell_data, list.mfirst (λ r : cell_data, f l r) cd) cd

meta def row_conflict (s : expr) (cd : list cell_data) : tactic unit :=
loop cd $ mk_row_conflict s

meta def col_conflict (s : expr) (cd : list cell_data) : tactic unit :=
loop cd $ mk_col_conflict s

meta def cell_conflict (s : expr) (cd : list cell_data) : tactic unit :=
loop cd $ mk_cell_conflict s

meta def box_conflict (s : expr) (cd : list cell_data) : tactic unit :=
loop cd $ mk_box_conflict s

meta def box_logic (r c v : pexpr) : tactic unit :=
do
  s ← get_sudoku,
  h ← to_expr ``(sudoku.box_cases %%s %%r %%c %%v),
  n ← mk_fresh_name,
  note n none h,
  tactic.repeat (auto_cases >> skip)

meta def row_logic (r v : pexpr) : tactic unit :=
do
  s ← get_sudoku,
  h ← to_expr ``(sudoku.row_cases %%s %%r %%v),
  n ← mk_fresh_name,
  note n none h,
  tactic.repeat (auto_cases >> skip)

meta def col_logic (c v : pexpr) : tactic unit :=
do
  s ← get_sudoku,
  h ← to_expr ``(sudoku.col_cases %%s %%c %%v),
  n ← mk_fresh_name,
  note n none h,
  tactic.repeat (auto_cases >> skip)

meta def cell_logic (r c : pexpr) : tactic unit :=
do
  s ← get_sudoku,
  h ← to_expr ``(sudoku.cell_cases %%s %%r %%c),
  n ← mk_fresh_name,
  note n none h,
  tactic.repeat (auto_cases >> skip)

meta def conflict' (s : expr) (cd : list cell_data) : tactic unit :=
row_conflict s cd <|> col_conflict s cd <|> cell_conflict s cd <|> box_conflict s cd

meta def conflict_with (s : expr) (cd : list cell_data) (e : expr) : tactic unit :=
do
  some d ← parse_cell_data s e,
  conflict' s (d::cd)

meta def conflict : tactic unit :=
do
  s ← get_sudoku,
  cd ← get_cell_data s,
  conflict' s cd

end tactic.sudoku

namespace tactic.interactive

open tactic.sudoku

setup_tactic_parser

meta def conflict : tactic unit :=
tactic.sudoku.conflict

meta def box_logic' (r c v : parse parser.pexpr) : tactic unit :=
tactic.sudoku.box_logic r c v

meta def row_logic' (r v : parse parser.pexpr) : tactic unit :=
tactic.sudoku.row_logic r v

meta def col_logic' (c v : parse parser.pexpr) : tactic unit :=
tactic.sudoku.col_logic c v

meta def cell_logic' (r c : parse parser.pexpr) : tactic unit :=
tactic.sudoku.cell_logic r c


meta def all_conflict : tactic unit :=
do
  s ← get_sudoku,
  cd ← get_cell_data s,
  tactic.all_goals (tactic.try (do
    e ← tactic.get_local `h,
    exfalso >> tactic.sudoku.conflict_with s cd e <|> tactic.exact e
  )) >> skip

meta def box_logic : tactic unit :=
do
  `(sudoku.f %%s (%%r, %%c) = %%v) ← target,
  tactic.sudoku.box_logic ``(((%%r).1 / 3 : ℕ)) ``(((%%c).1 / 3 : ℕ)) (pexpr.of_expr v),
  all_conflict

meta def row_logic : tactic unit :=
do
  `(sudoku.f %%s (%%r, %%c) = %%v) ← target,
  tactic.sudoku.row_logic (pexpr.of_expr r) (pexpr.of_expr v),
  all_conflict

meta def col_logic : tactic unit :=
do
  `(sudoku.f %%s (%%r, %%c) = %%v) ← target,
  tactic.sudoku.col_logic (pexpr.of_expr c) (pexpr.of_expr v),
  all_conflict

meta def cell_logic : tactic unit :=
do
  `(sudoku.f %%s (%%r, %%c) = %%v) ← target,
  tactic.sudoku.cell_logic (pexpr.of_expr r) (pexpr.of_expr c),
  all_conflict

meta def naked_single : tactic unit :=
cell_logic


end tactic.interactive
