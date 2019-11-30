import system.io
open nat io

def hello_world : io unit :=
  put_str "hello world\n"

#eval hello_world


def print_squares : ℕ → io unit
| 0          := return ()
| (succ n)   := print_squares n >>
                put_str (to_string n ++ "^2 = " ++ to_string (n * n) ++ "\n")

#eval print_squares 100

meta def m91 : ℕ -> ℕ
| n := if n > 100 then n - 10 else m91 (m91 (n + 11))

#eval m91 10
#eval m91 100

meta def foo: ℕ -> ℕ
| n:= foo n + 1

#reduce foo
