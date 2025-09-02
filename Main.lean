import GradPL

def hello : String := "World"

def main : IO Unit :=
  IO.println s!"Hello, {hello}!"
