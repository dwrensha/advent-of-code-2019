import system.io data.buffer.parser
open parser

def go {α} (file : string) (p : parser α) (m: α → option string) : io unit :=
do s ← io.fs.read_file file,
  sum.inr a ← return $ run p s,
  some str ← return $ m a,
  trace str (return ())

def parse_words := sep_by (do _ ← sat char.is_whitespace, return ()) (many (sat char.is_alpha))

def day_2 := go "src/2018-day-2-input.txt" parse_words

def helper2 : char → ℕ → bool → bool
| _ _ tt := tt
| _ 2 _ := tt
| _ _ _ := ff

def has_same_char_twice (m: rbmap char ℕ) : bool := m.fold helper2 ff

def helper3 : char → ℕ → bool → bool
| _ _ tt := tt
| _ 3 _ := tt
| _ _ _ := ff

def has_same_char_thrice (m: rbmap char ℕ) : bool := m.fold helper3 ff

def make_tree : list char → rbmap char ℕ → rbmap char ℕ
| [] acc := acc
| (c::cs) acc := match acc.find_entry c with
                   | some kv := make_tree cs (acc.insert c (kv.snd + 1))
                   | none := make_tree cs (acc.insert c 1)
                   end


def iter : list (list char) → ℕ → ℕ → option string
| [] twice thrice := some $ to_string (twice * thrice)
| (w::ws) twice thrice :=
     let t := make_tree w (mk_rbmap _ _) in
     let twice' := if has_same_char_twice t then twice + 1 else twice in
     let thrice' := if has_same_char_thrice t then thrice + 1 else thrice in
     iter ws twice' thrice'

#eval day_2 $ λ l, iter l 0 0 -- 5928


def word_diff : list char → list char → ℕ → ℕ
| [] [] n := n
| [] (c::cs) _ := 100 -- arbitrary number larger than 1
| (c::cs) [] _ := 100 -- arbitrary number larger than 1
| (c::cs) (d::ds) n :=
  let inc := if c = d then 0 else 1 in
  word_diff cs ds (n + inc)

def common_letters : list char → list char → list char
| [] [] := []
| (c::cs) (d::ds) :=
  if c = d then c::(common_letters cs ds)
  else common_letters cs ds
| _ _ := [] -- would be better to indicate failure

meta def iter2: list (list char) → list (list char) → option string
| [] [] := none
| [] (v::vs) := iter2 vs vs
| (w::ws) (v::vs) := if word_diff w v 0 = 1 then some (common_letters w v).as_string
                     else iter2 ws (v::vs)
| _ _ := none

#eval day_2 $ λ l, iter2 l l
