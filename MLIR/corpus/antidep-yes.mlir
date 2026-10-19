// antidependence: A[i] := A[i+1] + 1, run in parallel.
// Thread i reads A[i+1] and thread i+1 writes it, so w_{i+1} meets r_i: a WAR race.
// Expected verdict: racy.
"builtin.module"() ({
  "func.func"() ({
  ^bb0(%A: memref<8xi32>):
    "affine.parallel"() ({
    ^bb0(%i: index):
      %0 = "affine.load"(%A, %i) {map = affine_map<(d0) -> (d0 + 1)>} : (memref<8xi32>, index) -> i32
      %c1 = "arith.constant"() {value = 1 : i32} : () -> i32
      %1 = "arith.addi"(%0, %c1) : (i32, i32) -> i32
      "affine.store"(%1, %A, %i) {map = affine_map<(d0) -> (d0)>} : (i32, memref<8xi32>, index) -> ()
      "affine.yield"() : () -> ()
    }) {lowerBoundsMap = affine_map<() -> (0)>, steps = [1], upperBoundsMap = affine_map<() -> (7)>} : () -> ()
    "func.return"() : () -> ()
  }) {function_type = (memref<8xi32>) -> (), sym_name = "antidep"} : () -> ()
}) : () -> ()
