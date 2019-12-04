import system.io data.buffer.parser
open parser nat

def go {α} (file : string) (p : parser α) (m: α → option string) : io unit :=
do s ← io.fs.read_file file,
  sum.inr a ← return $ run p s,
  some str ← return $ m a,
  trace str (return ())

inductive step
| right : ℕ → step
| left : ℕ → step
| up : ℕ → step
| down : ℕ → step


def parse_number : parser ℕ := string.to_nat <$> many_char1 (sat char.is_digit)

def parse_step : parser step :=
  do
    c ← one_of ['R', 'L', 'U', 'D'],
    n ← parse_number,
    --trace ((to_string c) ++ (to_string n)) (return ()),
    return (match c with | 'R' := step.right n
                         | 'L' := step.left n
                         | 'U' := step.up n
                         | 'D' := step.down n
                         | _ := sorry
            end)

def parse_wires : parser (list step × list step) :=
  do
   wire1 ← sep_by (ch ',') parse_step,
   ch '\n',
   wire2 ← sep_by (ch ',') parse_step,
   ch '\n',
   return ⟨wire1, wire2⟩

def day03 := go "day03.txt" parse_wires

#eval day03 $ λ _, some "SUCCESS"

meta def walk_wire {T : Type} (f: ℤ×ℤ → T → T) : list step → ℤ×ℤ → T → T
| [] _ acc := acc
| ( (step.left 0)::ss) cur_pos acc := walk_wire ss cur_pos acc
| ( (step.right 0)::ss) cur_pos acc := walk_wire ss cur_pos acc
| ( (step.up 0)::ss) cur_pos acc := walk_wire ss cur_pos acc
| ( (step.down 0)::ss) cur_pos acc := walk_wire ss cur_pos acc
| ( (step.left (succ s))::ss) cur_pos acc :=
 let new_pos : ℤ × ℤ := ⟨cur_pos.1 - 1, cur_pos.2⟩ in
 walk_wire ((step.left s)::ss) new_pos (f new_pos acc)
| ( (step.right (succ s))::ss) cur_pos acc :=
 let new_pos : ℤ × ℤ := ⟨cur_pos.1 + 1, cur_pos.2⟩ in
 walk_wire ((step.right s)::ss) new_pos (f new_pos acc)
| ( (step.up (succ s))::ss) cur_pos acc :=
 let new_pos : ℤ × ℤ := ⟨cur_pos.1, cur_pos.2 + 1⟩ in
 walk_wire ((step.up s)::ss) new_pos (f new_pos acc)
| ( (step.down (succ s))::ss) cur_pos acc :=
 let new_pos : ℤ × ℤ := ⟨cur_pos.1, cur_pos.2 - 1⟩ in
 walk_wire ((step.down s)::ss) new_pos (f new_pos acc)

meta def construct_map : list step → ℤ×ℤ → rbtree (ℤ × ℤ) → rbtree (ℤ × ℤ) :=
walk_wire (λ pos acc, acc.insert pos)

def manhattan (p : ℤ×ℤ) : ℤ :=
abs (p.1) + abs (p.2)

def find_closest (wire1_tree: rbtree (ℤ×ℤ)) : ℤ×ℤ → (ℤ×ℤ) → ℤ×ℤ
| new_pos prev_closest :=
  if wire1_tree.contains new_pos then
    let new_manhattan := manhattan new_pos in
    let new_closest := if new_manhattan < manhattan prev_closest then new_pos else prev_closest in
    new_closest
  else prev_closest

--#eval day03 $ λ wires,
--  let map := construct_map wires.1 ⟨0,0⟩ (mk_rbtree _ _) in
--  let closest_pos := walk_wire (find_closest map) wires.2 ⟨0,0⟩ ⟨100000000,10000000⟩ in
--  let dist := manhattan closest_pos in
--  some $ to_string dist


meta def construct_map2 : list step → ℤ×ℤ → ℤ × (rbmap (ℤ × ℤ) ℤ) → ℤ × rbmap (ℤ × ℤ) ℤ :=
walk_wire (λ pos acc,
  if acc.2.contains pos then ⟨acc.1 + 1, acc.2⟩
  else ⟨acc.1 + 1, acc.2.insert pos acc.1⟩)

--                                                (dist, prev_best)
def find_closest2 (wire1_map: rbmap (ℤ×ℤ) ℤ) : ℤ×ℤ → (ℤ×ℤ) → (ℤ×ℤ)
| new_pos acc :=
  match wire1_map.find new_pos with
     | some wire_1_dist :=
           let new_dist := wire_1_dist + acc.1 in
           let new_best := if new_dist < acc.2 then new_dist else acc.2 in
           ⟨acc.1 + 1, new_best⟩
     | none := ⟨acc.1 + 1, acc.2⟩
  end

#eval day03 $ λ wires,
  let ⟨_, map⟩ := construct_map2 wires.1 ⟨0,0⟩ ⟨0, (mk_rbmap _ _)⟩ in
  let ⟨_, closest⟩ := walk_wire (find_closest2 map) wires.2 ⟨0,0⟩ ⟨0,10000000⟩ in
  some $ to_string closest
