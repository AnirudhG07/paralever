// a two-dimensional parallel loop over a 3x4 matrix: C[i,j] := A[i,j] * 2.
// The affine map (d0, d1) -> (d0, d1) is read as a row-major subscript through the buffer's
// own strides, so each thread's footprint is one cell of each buffer and the twelve threads
// are pairwise independent. Expected verdict: race-free.
"builtin.module"() ({
  "memref.global"() {sym_name = "A", type = memref<3x4xi32>, initial_value = dense<[[1, 2, 3, 4], [5, 6, 7, 8], [9, 10, 11, 12]]>} : () -> ()
  "func.func"() ({
    %A = "memref.get_global"() {name = @A} : () -> memref<3x4xi32>
    %C = "memref.alloc"() : () -> memref<3x4xi32>
    "affine.parallel"() ({
    ^bb0(%i: index, %j: index):
      %c2 = "arith.constant"() {value = 2 : i32} : () -> i32
      %0 = "affine.load"(%A, %i, %j) {map = affine_map<(d0, d1) -> (d0, d1)>} : (memref<3x4xi32>, index, index) -> i32
      %1 = "arith.muli"(%0, %c2) : (i32, i32) -> i32
      "affine.store"(%1, %C, %i, %j) {map = affine_map<(d0, d1) -> (d0, d1)>} : (i32, memref<3x4xi32>, index, index) -> ()
      "affine.yield"() : () -> ()
    }) {lowerBoundsMap = affine_map<() -> (0, 0)>, steps = [1, 1], upperBoundsMap = affine_map<() -> (3, 4)>} : () -> ()
    "func.return"() : () -> ()
  }) {function_type = () -> (), sym_name = "nested2d"} : () -> ()
}) : () -> ()
