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
list.erase_dup ∘ list.filter_map
  (λ cd : cell_data, if cd.row.1 = n ∧ cd.col.1 = m then some (
    if cd.val.1 = 0 then 9 else cd.val.1) else none)

meta def mk_table_entry (n m : ℕ) (cd : list cell_data) : tactic (html empty) :=
do
  let attrs : list (attr empty) := [cn "bw2"],
  let attrs := if n % 3 = 0 then attrs ++ [cn "bt"] else attrs,
  let attrs := if m % 3 = 0 then attrs ++ [cn "bl"] else attrs,
  let attrs := if n % 3 = 2 then attrs ++ [cn "bb"] else attrs,
  let attrs := if m % 3 = 2 then attrs ++ [cn "br"] else attrs,
  let ns := get_numbers n m cd,
  let s : string := match ns with
  | [] := ""
  | (a::[]) := to_string a
  | (a::as) := "💥"
  end,
  return $ h "td" attrs [
    h "div" [cn "dt", cn "ba", cn "b--light-silver", cn "w3", cn "h3"] [
      h "p" [cn "dtc", cn "v-mid", cn "tc", cn "f2"] s
    ]
  ]

meta def mk_table_row (n : ℕ) (cd : list cell_data) : tactic (html empty) :=
do
  a ← list.mmap (λ m, mk_table_entry n m cd) (list.iota' 9),
  return $ h "tr" [] a

meta def mk_table (cd : list cell_data) : tactic (html empty) :=
do
  a ← list.mmap (λ n, mk_table_row n cd) (list.iota' 9),
  return $ h "table" [cn "collapse"] a

meta def sudoku_widget : tactic (list (html empty)) :=
do
  s ← get_sudoku,
  cd ← get_cell_data s,
  g ← local_context,
  u ← mk_table cd,
  return [u]

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
