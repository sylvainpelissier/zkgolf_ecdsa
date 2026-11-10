import Lake
open Lake DSL
package ECDSAGolf
require clean from git "https://github.com/Verified-zkEVM/clean" @ "93c9d1ef45be9f687214625d7857889cf2485504"
require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "5ed2965256430c3649e86755f9576b54eca72435"
@[default_target] lean_lib Challenge
lean_lib Tests
@[default_target] lean_exe vectors where
  root := `Tests.Main

lean_lib ECDSA where
  srcDir := "vendor/longfellow"

lean_lib Baseline

lean_lib Optimized

lean_exe baselineCheck where
  root := `Baseline.Check

lean_lib Solution
