/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import init.meta.widget.tactic_component
import stactic

section tac
open tactic widget tactic.sudoku

meta def list.iota' : ℕ → list ℕ :=
list.map (λ n, n - 1) ∘ list.reverse ∘ list.iota

meta def get_numbers (n m : ℕ) : list cell_data → list ℕ :=
list.dedup ∘ list.filter_map
  (λ cd : cell_data, if cd.row.1 = n ∧ cd.col.1 = m then some (
    if cd.val.1 = 0 then 9 else cd.val.1) else none)

meta def get_outer_marks (n m : ℕ) : list outer_pencil_data → list ℕ :=
list.dedup ∘ list.filter_map
  (λ op : outer_pencil_data,
    if (op.row₀.1 = n ∧ op.col₀.1 = m) ∨ (op.row₁.1 = n ∧ op.col₁.1 = m) then some (
      if op.val.1 = 0 then 9 else op.val.1) else none)

meta def get_inner_marks (n m : ℕ) : list inner_pencil_data → list ℕ :=
list.head ∘ list.filter_map
  (λ ip : inner_pencil_data,
    if ip.row.1 = n ∧ ip.col.1 = m then some (list.map
      (λ k : fin 9, if k.1 = 0 then 9 else k.1) ip.vals) else none)

meta def format_marks (n m : ℕ) (bi : board_info) : list (html empty) :=
match get_inner_marks n m bi.ip with
| [] := let os := get_outer_marks n m bi.op in
  [h "div" [cn "dtc", cn "mw3", cn "flex", cn "flex-wrap"]
    (list.map (λ k : ℕ, h "span" [cn "f5", cn "ph1"] [to_string k]) os)]
| l := [h "span" [cn "dtc", cn "tc", cn "v-mid", cn "f5"] (list.map (λ l : ℕ, to_string l) l)]
end

meta def mk_table_entry (n m : ℕ) (bi : board_info) : tactic (html empty) :=
do
  let attrs : list (attr empty) := [cn "bw2"],
  let attrs := if n % 3 = 0 then attrs ++ [cn "bt"] else attrs,
  let attrs := if m % 3 = 0 then attrs ++ [cn "bl"] else attrs,
  let attrs := if n % 3 = 2 then attrs ++ [cn "bb"] else attrs,
  let attrs := if m % 3 = 2 then attrs ++ [cn "br"] else attrs,
  let ns := get_numbers n m bi.cd,
  let s : list (html empty) := match ns with
  | [] := format_marks n m bi
  | (a::[]) := [h "span" [cn "dtc", cn "v-mid", cn "tc", cn "f2"] [to_string a]]
  | (a::as) := [h "span" [cn "dtc", cn "v-mid", cn "tc", cn "f2"] ["💥"]]
  end,
  return $ h "td" attrs [
    h "div" [cn "dt", cn "ba", cn "b--light-silver", cn "w3", cn "mw3", cn "h3"] s
  ]

meta def mk_table_row (n : ℕ) (bi : board_info) : tactic (html empty) :=
do
  a ← list.mmap (λ m, mk_table_entry n m bi) (list.iota' 9),
  return $ h "tr" [] a

meta def mk_table (bi : board_info) : tactic (html empty) :=
do
  a ← list.mmap (λ n, mk_table_row n bi) (list.iota' 9),
  return $ h "table" [cn "collapse"] a

meta def sudoku_widget : tactic (list (html empty)) :=
(do
  s ← get_sudoku,
  bi ← get_board_info s,
  u ← mk_table bi,
  return [u]) <|> return []

end tac

section tc

open widget

meta def sudoku_component : tc unit empty :=
tc.stateless $ λ _, sudoku_widget

meta def combined_component : tc unit empty :=
tc.stateless $ λ _,
do
  s ← tactic.read,
  return [
    h "div" [] [html.of_component s (tc.to_component sudoku_component)],
    h "hr" [] [],
    h "div" [] [html.of_component s tactic_state_widget]
  ]

end tc

@[reducible] meta def show_sudoku := tactic

open tactic

-- The following two functions are taken from the natural number game and are written by Rob Lewis

meta def copy_decl (d : declaration) : tactic unit :=
add_decl $ d.update_name $ d.to_name.update_prefix `show_sudoku.interactive

meta def copy_decls : tactic unit :=
do env ← get_env,
  let ls := env.fold [] list.cons,
  ls.mmap' $ λ dec, when (dec.to_name.get_prefix = `tactic.interactive) (copy_decl dec)

namespace show_sudoku

meta def step {α : Type} (t : show_sudoku α) : show_sudoku unit :=
t >> return ()

meta def istep := @tactic.istep

meta def solve1 := @tactic.solve1

meta def save_info (p : pos) : show_sudoku unit :=
do
  s ← tactic.read,
  tactic.save_info_thunk p (λ _, tactic_state.to_format s),
  tactic.save_widget p (widget.tc.to_component combined_component)

end show_sudoku

run_cmd copy_decls

example (P Q : Prop) (i : P → Q) (j : P) : Q :=
begin [show_sudoku]
  apply i,
  have : true := trivial,
  exact j,
end
