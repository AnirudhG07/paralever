// reduction with no reduction clause: sum[0] := sum[0] + A[i], run in parallel.
// Every thread writes the same cell, so w_i meets w_j and w_i meets r_j at once.
// Expected verdict: racy. The right answer would be 36; any schedule-dependent value is
// evidence of the race rather than of a translation fault.
"builtin.module"() ({
  "memref.global"() {sym_name = "A", type = memref<8xi32>, initial_value = dense<[1, 2, 3, 4, 5, 6, 7, 8]>} : () -> ()
  "func.func"() ({
    %A = "memref.get_global"() {name = @A} : () -> memref<8xi32>
    %sum = "memref.alloc"() : () -> memref<1xi32>
    "affine.parallel"() ({
    ^bb0(%i: index):
      %0 = "affine.load"(%A, %i) {map = affine_map<(d0) -> (d0)>} : (memref<8xi32>, index) -> i32
      %1 = "affine.load"(%sum, %i) {map = affine_map<(d0) -> (0)>} : (memref<1xi32>, index) -> i32
      %2 = "arith.addi"(%1, %0) : (i32, i32) -> i32
      "affine.store"(%2, %sum, %i) {map = affine_map<(d0) -> (0)>} : (i32, memref<1xi32>, index) -> ()
      "affine.yield"() : () -> ()
    }) {lowerBoundsMap = affine_map<() -> (0)>, steps = [1], upperBoundsMap = affine_map<() -> (8)>} : () -> ()
    "func.return"() : () -> ()
  }) {function_type = (), sym_name = "reduction"} : () -> ()
}) : () -> ()
