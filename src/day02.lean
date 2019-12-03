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


#eval day02 $ λ l,
  some (list.foldl (λ a: string, λb : ℕ, a ++ (to_string b) ++ ",") "" l)

