import «DeBruijnSn»

def hello : String := "world"

def main : IO Unit :=
  IO.println s!"Hello, {hello}!"
