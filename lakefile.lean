import Lake
open Lake DSL

package aoc22 {
  -- add package configuration options here
}

lean_lib Dec1
lean_lib Dec2
lean_lib Dec3

@[defaultTarget]
lean_exe aoc22 {
  root := `Main
}
