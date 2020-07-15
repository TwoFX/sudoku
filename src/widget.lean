import init.meta.widget.tactic_component

section tac
open tactic widget

meta def list.iota' : ℕ → list ℕ :=
list.map (λ n, n - 1) ∘ list.reverse ∘ list.iota

meta def mk_table_entry (n m : ℕ) : tactic (html empty) :=
do
  let attrs : list (attr empty) := [cn "bw2"],
  let attrs := if n % 3 = 0 then attrs ++ [cn "bt"] else attrs,
  let attrs := if m % 3 = 0 then attrs ++ [cn "bl"] else attrs,
  let attrs := if n % 3 = 2 then attrs ++ [cn "bb"] else attrs,
  let attrs := if m % 3 = 2 then attrs ++ [cn "br"] else attrs,
  let s := if n ≤ 8 ∧ m ≤ 8 then "7" else "",
  return $ h "td" attrs [
    h "div" [cn "dt", cn "ba", cn "b--light-silver", cn "w3", cn "h3"] [
      h "p" [cn "dtc", cn "v-mid", cn "tc", cn "f2"] s
    ]
  ]

meta def mk_table_row (n : ℕ) : tactic (html empty) :=
do
  a ← list.mmap (λ m, mk_table_entry n m) (list.iota' 9),
  return $ h "tr" [] a

meta def mk_table : tactic (html empty) :=
do
  a ← list.mmap (λ n, mk_table_row n) (list.iota' 9),
  return $ h "table" [cn "collapse"] a

meta def hello_world_tac : tactic (list (html empty)) :=
do
  g ← local_context,
  u ← mk_table,
  return [h "p" [] format!"Hello world! There are {list.length g} hypotheses!",
    u
  ]

end tac

section tc

open widget

meta def hello_world : tc unit empty :=
tc.stateless $ λ _, hello_world_tac

meta def combined : tc unit empty :=
tc.stateless $ λ _,
do
  s ← tactic.read,
  return [
    h "div" [] [html.of_component s (tc.to_component hello_world)],
    h "hr" [] [],
    h "div" [] [html.of_component s tactic_state_widget]
  ]

end tc

@[reducible] meta def hello_world_exec := tactic

open tactic

meta def copy_decl (d : declaration) : tactic unit :=
add_decl $ d.update_name $ d.to_name.update_prefix `hello_world_exec.interactive

meta def copy_decls : tactic unit :=
do env ← get_env,
  let ls := env.fold [] list.cons,
  ls.mmap' $ λ dec, when (dec.to_name.get_prefix = `tactic.interactive) (copy_decl dec)

namespace hello_world_exec

meta def step {α : Type} (t : hello_world_exec α) : hello_world_exec unit :=
t >> return ()

meta def istep := @tactic.istep

meta def save_info (p : pos) : hello_world_exec unit :=
do
  s ← tactic.read,
  tactic.save_info_thunk p (λ _, tactic_state.to_format s),
  tactic.save_widget p (widget.tc.to_component combined)

end hello_world_exec

run_cmd copy_decls

example (P Q : Prop) (i : P → Q) (j : P) : Q :=
begin [hello_world_exec]
  apply i,
  have : true := trivial,
  exact j,
end
