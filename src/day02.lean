import system.io data.buffer.parser
open parser nat

def go {α} (file : string) (p : parser α) (m: α → option string) : io unit :=
do s ← io.fs.read_file file,
  sum.inr a ← return $ run p s,
  some str ← return $ m a,
  trace str (return ())

def parse_number := string.to_nat <$> many_char1 (sat char.is_digit)

def day02 := go "day02.txt" ((many (parse_number <* ch ',')) <* ch '\n')

def nth : list ℕ → ℕ → ℕ
| [] _ := sorry
| (c::cs) 0 := c
| (c::cs) (succ idx) := nth cs idx

def replace_nth : list ℕ → ℕ → ℕ → list ℕ
| [] _ _ := sorry
| (c::cs) 0 new_value := new_value::cs
|  (c::cs) (succ idx) new_value := c::(replace_nth cs idx new_value)

-- map current memory, current pointer, to ending memory
meta def execute : list ℕ → ℕ → list ℕ
| m idx :=
let x := nth m idx in
if x = 99 then m
else
  let arg1 := nth m (idx + 1) in
  let arg2 := nth m (idx + 2) in
  let arg3 := nth m (idx + 3) in
  let inp1 := nth m arg1 in
  let inp2 := nth m arg2 in
  let new_value := if x = 1 then inp1 + inp2
                   else if x = 2 then inp1 * inp2
                   else sorry in
  let new_list := replace_nth m arg3 new_value in
  execute new_list (idx + 4)

#eval day02 $ λ l,
  let l' := replace_nth l 1 12 in
  let l'' := replace_nth l' 2 2 in
  let final := execute l'' 0 in
  to_string (nth final 0)


--#eval day02 $ λ l,   some (list.foldl (λ a: string, λb : ℕ, a ++ (to_string b) ++ ",") "" l)

meta def do_with_inputs : list ℕ → ℕ → ℕ → ℕ
| l inp1 inp2 :=
  let l' := replace_nth l 1 inp1 in
  let l'' := replace_nth l' 2 inp2 in
  let final := execute l'' 0 in
  nth final 0

meta def iter (mem: list ℕ) (goal: ℕ) : ℕ → ℕ → option string
| 100 100 := none
| 100 n := iter 0 (n+1)
| n m := if do_with_inputs mem n m = goal then some (to_string (100 * n + m))
                     else iter (n+1) m

-- #eval day02 $ λ l, iter l 19690720 0 0

-- let's try to do it faster...

def read_or_sorry {s : ℕ} (m: array s ℕ) (idx: ℕ) : ℕ :=
if h : idx < s then m.read ⟨idx, h⟩ else sorry

def write_or_sorry {s : ℕ} (m : array s ℕ) (idx : ℕ) (new_value : ℕ) : array s ℕ :=
if h : idx < s then m.write ⟨idx, h⟩ new_value else sorry

meta def array_execute {s : ℕ} : array s ℕ → ℕ → array s ℕ
| m idx :=
let x := read_or_sorry m idx in
if x = 99 then m
else
  let arg1 := read_or_sorry m (idx + 1) in
  let arg2 := read_or_sorry m (idx + 2) in
  let arg3 := read_or_sorry m (idx + 3) in
  let inp1 := read_or_sorry m arg1 in
  let inp2 := read_or_sorry m arg2 in
  let new_value := if x = 1 then inp1 + inp2
                   else if x = 2 then inp1 * inp2
                   else sorry in
  let new_array := write_or_sorry m arg3 new_value in
  array_execute new_array (idx + 4)


def list_to_array_helper {s : ℕ} : (array s ℕ) → ℕ → list ℕ → array s ℕ
| a _ [] := a
| a idx (c::cs) := list_to_array_helper (write_or_sorry a idx c) (idx + 1) cs

def list_to_array (l : list ℕ) : array (list.length l) ℕ :=
  let len := list.length l in
  let zeros : array len ℕ := ⟨λ _, 0⟩ in
  list_to_array_helper zeros 0 l

#eval day02 $ λ l,
  let l' := replace_nth l 1 12 in
  let l'' := replace_nth l' 2 2 in
  let final := array_execute (list_to_array l'') 0 in
  to_string (read_or_sorry final 0)


meta def array_do_with_inputs {s : ℕ} : array s ℕ → ℕ → ℕ → ℕ
| a inp1 inp2 :=
  let a' := write_or_sorry a 1 inp1 in
  let a'' := write_or_sorry a' 2 inp2 in
  let final := array_execute a'' 0 in
  read_or_sorry final 0

meta def array_iter {s : ℕ} (mem: array s ℕ) (goal: ℕ) : ℕ → ℕ → option string
| 100 100 := none
| 100 n := array_iter 0 (n+1)
| n m := if array_do_with_inputs mem n m = goal then some (to_string (100 * n + m))
                     else array_iter (n+1) m

#eval day02 $ λ l, array_iter (list_to_array l) 19690720 0 0
