/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import basic
import tactic.norm_num
import init.meta.has_reflect

universes u v w

open tactic

def list.mfirst' {m : Type → Type v} [monad m] {α : Type} [inhabited α] (f : α → m bool) : list α → m α
| [] := return default
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

meta structure cell_data :=
(row col val : fin 9)
(e re ce ve : expr)

meta structure outer_pencil_data :=
(row₀ col₀ row₁ col₁ val : fin 9)
(e : expr)

meta structure inner_pencil_data :=
(row col : fin 9)
(vals : list (fin 9))
(e : expr)

meta structure board_info :=
(cd : list cell_data)
(op : list outer_pencil_data)
(ip : list inner_pencil_data)

meta instance format_cell_data : has_to_format cell_data :=
{ to_format := λ d,
  format!"{cell_data.e d}" }

meta def eval_fin : expr → fin 9
| `(bit1 %%e) := let i := eval_fin e in ⟨(2 * i.1 + 1) % 9, nat.mod_lt _ $ nat.zero_lt_succ _⟩
| `(bit0 %%e) := let i := eval_fin e in ⟨(2 * i.1) % 9, nat.mod_lt _ $ nat.zero_lt_succ _⟩
| `(has_one.one) := 1
| `(has_zero.zero) := 0
| `(coe %%e) := eval_fin e
| `(%%e * %%f) := let i := eval_fin e, j := eval_fin f in ⟨(i.1 * j.1) % 9, nat.mod_lt _ $ nat.zero_lt_succ _⟩
| `(%%e + %%f) := let i := eval_fin e, j := eval_fin f in ⟨(i.1 + j.1) % 9, nat.mod_lt _ $ nat.zero_lt_succ _⟩
| `(%%e / %%f) := let i := eval_fin e, j := eval_fin f in ⟨(i.1 / j.1) % 9, nat.mod_lt _ $ nat.zero_lt_succ _⟩
| `(subtype.val %%e) := eval_fin e
| _ := 0

meta def parse_cell_data (s e : expr) : tactic (option cell_data) :=
(do
  `(sudoku.f %%s (%%a, %%b) = %%c) ← infer_type e,
  let u := eval_fin a,
  let v := eval_fin b,
  let w := eval_fin c,
  return $ some ⟨u, v, w, e, a, b, c⟩) <|> return none

meta def parse_outer_pencil_data (s e : expr) : tactic (option outer_pencil_data) :=
(do
  `(sudoku.snyder %%s %%r₀ %%c₀ %%r₁ %%c₁ %%v) ← infer_type e,
  [pr₀, pc₀, pr₁, pc₁, pv] ← list.mmap (eval_expr (fin 9)) [r₀, c₀, r₁, c₁, v],
  return $ some ⟨pr₀, pc₀, pr₁, pc₁, pv, e⟩) <|> return none

meta def parse_inner_pencil_data₂ (s e : expr) : tactic (option inner_pencil_data) :=
(do
  `(sudoku.double %%s %%r %%c %%v₁ %%v₂) ← infer_type e,
  [pr, pc, pv₁, pv₂] ← list.mmap (eval_expr (fin 9)) [r, c, v₁, v₂],
  return $ some ⟨pr, pc, [pv₁, pv₂], e⟩) <|> return none

meta def parse_inner_pencil_data₃ (s e : expr) : tactic (option inner_pencil_data) :=
(do
  `(sudoku.triple %%s %%r %%c %%v₁ %%v₂ %%v₃) ← infer_type e,
  [pr, pc, pv₁, pv₂, pv₃] ← list.mmap (eval_expr (fin 9)) [r, c, v₁, v₂, v₃],
  return $ some ⟨pr, pc, [pv₁, pv₂, pv₃], e⟩) <|> return none

meta def parse_inner_pencil_data (s e : expr) : tactic (option inner_pencil_data) :=
do
  t ← parse_inner_pencil_data₂ s e,
  match t with
  | some d := return $ some d
  | none := parse_inner_pencil_data₃ s e
  end

meta def get_cell_data (s : expr) : tactic (list cell_data) :=
local_context >>= list.mfiltermap (parse_cell_data s)

meta def get_outer_pencil_data (s : expr) : tactic (list outer_pencil_data) :=
local_context >>= list.mfiltermap (parse_outer_pencil_data s)

meta def get_inner_pencil_data (s : expr) : tactic (list inner_pencil_data) :=
local_context >>= list.mfiltermap (parse_inner_pencil_data s)

meta def get_board_info (s : expr) : tactic board_info :=
do
  cd ← get_cell_data s,
  op ← get_outer_pencil_data s,
  ip ← get_inner_pencil_data s,
  return ⟨cd, op, ip⟩

meta def mk_neq (l r : fin 9) : tactic expr :=
do
  bla ← to_expr ``(%%(nat.reflect l.val) ≠ %%(nat.reflect r.val)),

  -- Don't try this at home kids
  (_, `(eq_true_intro %%a)) ← norm_num.eval_ineq bla,
  return a

meta def mk_app_stupid_aux : expr → list expr → expr
| s [] := s
| s (t::ts) := expr.app (mk_app_stupid_aux s ts) t

meta def mk_app_stupid' (s : expr) (ls : list expr) : expr :=
mk_app_stupid_aux s ls.reverse

meta def mk_app_stupid (n : name) (ls : list expr) : expr :=
mk_app_stupid' (expr.const n []) ls

meta def nine : tactic expr := to_expr ``(9)

meta def mk_neq' (l r : fin 9) (a b : expr) : tactic expr :=
do
  n ← mk_fresh_name,
  bla ← to_expr ``(%%a ≠ %%b),
  u ← mk_neq l r, -- u states that l.1 ≠ r.1
  f ← tactic.assert n bla,
  h ← mk_fresh_name,
  e ← tactic.intro h,
  ni ← nine,
  let i := mk_app_stupid `fin.veq_of_eq [ni, a, b, e],
  let j := expr.app u i,
  tactic.exact j,
  return f

meta def mk_row_conflict (s : expr) (l r : cell_data) : tactic unit :=
do
  guard (l.row = r.row),
  guard (l.val = r.val),
  guard (l.col ≠ r.col),
  f ← mk_neq' l.col r.col l.ce r.ce,
  tactic.exact (mk_app_stupid `sudoku.row_conflict [s, l.re, l.ce, r.ce, l.ve, l.e, r.e, f])

meta def mk_col_conflict (s : expr) (l r : cell_data) : tactic unit :=
do
  guard (l.row ≠ r.row),
  guard (l.val = r.val),
  guard (l.col = r.col),
  f ← mk_neq' l.row r.row l.re r.re,
  tactic.exact (mk_app_stupid `sudoku.col_conflict [s, l.re, r.re, l.ce, l.ve, l.e, r.e, f])

meta def mk_cell_conflict (s : expr) (l r : cell_data) : tactic unit :=
do
  guard (l.row = r.row),
  guard (l.col = r.col),
  guard (l.val ≠ r.val),
  f ← mk_neq' l.val r.val l.ve r.ve,
  tactic.exact (mk_app_stupid `sudoku.cell_conflict [s, l.re, l.ce, l.ve, r.ve, l.e, r.e, f])

meta def mk_box_conflict (s : expr) (l r : cell_data) : tactic unit :=
do
  guard (l.val = r.val),
  guard (l.row / 3 = r.row / 3),
  guard (l.col / 3 = r.col / 3),
  guard (l.row ≠ r.row ∨ l.col ≠ r.col),
  e₁ ← to_expr ``(sudoku.box_conflict %%s %%l.e %%r.e rfl rfl),
  (if l.row ≠ r.row then do f ← mk_neq l.row r.row, to_expr ``(%%e₁ (or.inl (λ h, %%f (fin.veq_of_eq h))))
    else do f ← mk_neq l.col r.col, to_expr ``(%%e₁ (λ h, (or.inr %%f (fin.veq_of_eq h))))) >>= tactic.exact

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

meta def split_cases (n : name) : tactic unit :=
tactic.repeat (do
  e ← get_local n,
  tactic.cases e [n, n],
  skip)

meta def box_logic (r c v : pexpr) (n : name) : tactic unit :=
do
  s ← get_sudoku,
  h ← to_expr ``(sudoku.box_cases %%s %%r %%c %%v),
  note n none h,
  split_cases n

meta def row_logic (r v : pexpr) (n : name) : tactic unit :=
do
  s ← get_sudoku,
  h ← to_expr ``(sudoku.row_cases %%s %%r %%v),
  note n none h,
  split_cases n

meta def col_logic (c v : pexpr) (n : name) : tactic unit :=
do
  s ← get_sudoku,
  h ← to_expr ``(sudoku.col_cases %%s %%c %%v),
  note n none h,
  split_cases n

meta def cell_logic (r c : pexpr) (n : name) : tactic unit :=
do
  s ← get_sudoku,
  h ← to_expr ``(sudoku.cell_cases %%s %%r %%c),
  note n none h,
  split_cases n

meta def conflict' (s : expr) (cd : list cell_data) : tactic unit :=
exfalso >> (row_conflict s cd <|> col_conflict s cd <|> cell_conflict s cd <|> box_conflict s cd)

meta def conflict_with (s : expr) (cd : list cell_data) (es : list expr) : tactic unit :=
do
  ds ← list.mfiltermap (parse_cell_data s) es,
  conflict' s (list.append ds cd)

meta def conflict : tactic unit :=
do
  s ← get_sudoku,
  cd ← get_cell_data s,
  conflict' s cd

meta def sudoku_exact (cd : cell_data) (r c v : fin 9) : tactic unit :=
do
  guard (r = cd.row),
  guard (c = cd.col),
  guard (v = cd.val),
  tactic.exact cd.e

meta def sudoku_assumption (s : expr) (cd : list cell_data) : tactic unit :=
do
  t ← target,
  match t with
  | `(sudoku.f %%s (%%r, %%c) = %%v) :=
    do
      [pr, pc, pv] ← return $ list.map eval_fin [r, c, v],
      list.mfirst (λ c : cell_data, sudoku_exact c pr pc pv) cd
  | `(sudoku.snyder %%s %%r₁ %%c₁ %%r₂ %%c₂ %%v) :=
    do
      [pr₁, pc₁, pr₂, pc₂, pv] ← return $ list.map eval_fin [r₁, c₁, r₂, c₂, v],
      (left >> list.mfirst (λ c : cell_data, sudoku_exact c pr₁ pc₁ pv) cd) <|>
        (right >> list.mfirst (λ c : cell_data, sudoku_exact c pr₂ pc₂ pv) cd)
  | `(sudoku.double %%s %%r %%c %%v₁ %%v₂) :=
    do
      [pr, pc, pv₁, pv₂] ← return $ list.map eval_fin [r, c, v₁, v₂],
      (left >> list.mfirst (λ c : cell_data, sudoku_exact c pr pc pv₁) cd) <|>
        (right >> list.mfirst (λ c : cell_data, sudoku_exact c pr pc pv₂) cd)
  | `(sudoku.triple %%s %%r %%c %%v₁ %%v₂ %%v₃) :=
    do
      [pr, pc, pv₁, pv₂, pv₃] ← return $ list.map eval_fin [r, c, v₁, v₂, v₃],
      (left >> list.mfirst (λ c : cell_data, sudoku_exact c pr pc pv₁) cd) <|>
        (right >> left >> list.mfirst (λ c : cell_data, sudoku_exact c pr pc pv₂) cd) <|>
        (right >> right >> list.mfirst (λ c : cell_data, sudoku_exact c pr pc pv₃) cd)
  | _ := tactic.split >> skip
  end

end tactic.sudoku

namespace tactic.interactive

open tactic.sudoku

setup_tactic_parser

meta def conflict : tactic unit :=
tactic.sudoku.conflict

meta def box_logic' (r c v : parse parser.pexpr) : tactic unit :=
tactic.sudoku.box_logic r c v `h

meta def row_logic' (r v : parse parser.pexpr) : tactic unit :=
tactic.sudoku.row_logic r v `h

meta def col_logic' (c v : parse parser.pexpr) : tactic unit :=
tactic.sudoku.col_logic c v `h

meta def cell_logic' (r c : parse parser.pexpr) : tactic unit :=
tactic.sudoku.cell_logic r c `h


meta def all_conflict (s : expr) (cd : list cell_data) (lems : list name) (ns : list name) : tactic unit :=
do
  let resolve_single (ns : list name) : tactic unit := (tactic.all_goals $ tactic.try (do
    es ← list.mmap get_local ns,
    tactic.sudoku.conflict_with s cd es <|>
      (parse_cell_data s es.head >>=
        (λ d, match d with | some d := sudoku_assumption s [d] | none := failed end))
      /-tactic.exact (list.head es) <|>
      (tactic.left >> tactic.exact es.head) <|>
      (tactic.right >> tactic.exact es.head) <|>
      (tactic.right >> tactic.left >> tactic.exact es.head) <|>
      (tactic.right >> tactic.right >> tactic.exact es.head)-/ )) >> skip,
  resolve_single ns,
  let idxs := (list.iota lems.length).reverse,
  list.mmap' (λ i : ℕ, do
    some n ← return $ lems.nth (i - 1),
    tactic.all_goals $ tactic.try $ (do e ← get_local n, tactic.cases e [n, n]),
    tactic.all_goals $ tactic.try $ (do e ← get_local n, tactic.cases e [n, n]),
    resolve_single ((lems.take i).append ns)) idxs

meta def box_logic (lems : parse with_ident_list) : tactic unit :=
do
  t ← target,
  (r, c, v) ← match t with
  | `(sudoku.f %%s (%%r, %%c) = %%v) := return (r, c, v)
  | `(sudoku.snyder %%s %%r₀ %%c₀ %%r₁ %%c₁ %%v) := return (r₀, c₀, v)
  | _ := tactic.fail "I don't recognize the goal."
  end,
  s ← get_sudoku,
  cd ← get_cell_data s,
  tactic.sudoku.box_logic ``(((%%r).1 / 3 : ℕ)) ``(((%%c).1 / 3 : ℕ)) (pexpr.of_expr v) `h,
  all_conflict s cd lems [`h]

meta def row_logic : tactic unit :=
do
  s ← get_sudoku,
  cd ← get_cell_data s,
  `(sudoku.f %%s (%%r, %%c) = %%v) ← target,
  tactic.sudoku.row_logic (pexpr.of_expr r) (pexpr.of_expr v) `h,
  all_conflict s cd [] [`h]

meta def col_logic : tactic unit :=
do
  s ← get_sudoku,
  cd ← get_cell_data s,
  `(sudoku.f %%s (%%r, %%c) = %%v) ← target,
  tactic.sudoku.col_logic (pexpr.of_expr c) (pexpr.of_expr v) `h,
  all_conflict s cd [] [`h]

meta def cell_logic (lems : parse with_ident_list) : tactic unit :=
do
  t ← target,
  (r, c) ← match t with
  | `(sudoku.f %%s (%%r, %%c) = %%v) := return (r, c)
  | `(sudoku.double %%s %%r %%c %%v₁ %%v₂) := return (r, c)
  | `(sudoku.triple %%s %%r %%c %%v₁ %%v₂ %%v₃) := return (r, c)
  | _ := tactic.fail "I don't recognize the goal"
  end,
  s ← get_sudoku,
  cd ← get_cell_data s,
  tactic.sudoku.cell_logic (pexpr.of_expr r) (pexpr.of_expr c) `h,
  all_conflict s cd lems [`h]

meta def pencil (lems : parse with_ident_list) : tactic unit :=
do
  s ← get_sudoku,
  cd ← get_cell_data s,
  all_conflict s cd lems []

meta def naked_single : parse with_ident_list → tactic unit :=
cell_logic

meta def sudoku_finish : tactic unit :=
do
  s ← get_sudoku,
  cd ← get_cell_data s,
  tactic.repeat $ sudoku_assumption s cd


end tactic.interactive
