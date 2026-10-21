import Tool

/-- The `paralever` executable: one command, one file. `paralever --help` is the grammar. -/
def main (args : List String) : IO UInt32 := Paralever.Tool.main args
