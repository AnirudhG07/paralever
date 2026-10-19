// doall: C[i] := A[i] + B[i], every iteration independent.
// Writes are disjoint singletons and no thread reads a cell another writes.
// Expected verdict: race-free. Expected result: C = [11, 22, 33, 44, 55, 66, 77, 88].
"builtin.module"() ({
  "memref.global"() {sym_name = "A", type = memref<8xi32>, initial_value = dense<[1, 2, 3, 4, 5, 6, 7, 8]>} : () -> ()
  "memref.global"() {sym_name = "B", type = memref<8xi32>, initial_value = dense<[10, 20, 30, 40, 50, 60, 70, 80]>} : () -> ()
  "func.func"() ({
    %A = "memref.get_global"() {name = @A} : () -> memref<8xi32>
    %B = "memref.get_global"() {name = @B} : () -> memref<8xi32>
    %C = "memref.alloc"() : () -> memref<8xi32>
    "affine.parallel"() ({
    ^bb0(%i: index):
      %0 = "affine.load"(%A, %i) {map = affine_map<(d0) -> (d0)>} : (memref<8xi32>, index) -> i32
      %1 = "affine.load"(%B, %i) {map = affine_map<(d0) -> (d0)>} : (memref<8xi32>, index) -> i32
      %2 = "arith.addi"(%0, %1) : (i32, i32) -> i32
      "affine.store"(%2, %C, %i) {map = affine_map<(d0) -> (d0)>} : (i32, memref<8xi32>, index) -> ()
      "affine.yield"() : () -> ()
    }) {lowerBoundsMap = affine_map<() -> (0)>, steps = [1], upperBoundsMap = affine_map<() -> (8)>} : () -> ()
    "func.return"() : () -> ()
  }) {function_type = () -> (), sym_name = "doall"} : () -> ()
}) : () -> ()
