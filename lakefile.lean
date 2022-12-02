import Lake
open Lake DSL

package aoc22 {
  -- add package configuration options here
}

lean_lib Aoc22 {
  -- add library configuration options here
}

@[defaultTarget]
lean_exe aoc22 {
  root := `Main
}
