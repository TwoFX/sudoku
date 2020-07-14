import init.meta.widget.tactic_component

section tac
open tactic widget

meta def hello_world_tac : tactic (list (html empty)) :=
do
  g ← local_context,
  return [h "p" [] format!"Hello world! There are {list.length g} hypotheses!"]

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
