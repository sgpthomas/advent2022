import Lake
open Lake DSL

package aoc22 {
  -- add package configuration options here
}

lean_lib Utils
lean_lib Dec1
lean_lib Dec2
lean_lib Dec3
lean_lib Dec4
lean_lib Dec5
lean_lib Dec6
lean_lib Dec7
lean_lib Dec8
lean_lib Dec9
lean_lib Dec10
lean_lib Dec11
lean_lib Dec12

@[defaultTarget]
lean_exe aoc22 {
  root := `Main
}
