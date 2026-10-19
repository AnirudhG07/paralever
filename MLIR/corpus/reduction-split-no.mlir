// the reduction done right: each thread accumulates a disjoint pair of A into its own
// partial cell, then a sequential loop folds the partials. Reads overlap nothing and each
// thread writes one cell. Declares its arrays with memref.global and memref.alloc, so the
// initial heap is real and differential execution has something to compare.
// Expected verdict: race-free. Expected result: part = [3, 7, 11, 15], sum = 36.
"builtin.module"() ({
  "memref.global"() {sym_name = "A", type = memref<8xi32>, initial_value = dense<[1, 2, 3, 4, 5, 6, 7, 8]>} : () -> ()
  "func.func"() ({
    %A = "memref.get_global"() {name = @A} : () -> memref<8xi32>
    %part = "memref.alloc"() : () -> memref<4xi32>
    %sum = "memref.alloc"() : () -> memref<1xi32>
    "affine.parallel"() ({
    ^bb0(%t: index):
      %0 = "affine.load"(%A, %t) {map = affine_map<(d0) -> (d0 * 2)>} : (memref<8xi32>, index) -> i32
      %1 = "affine.load"(%A, %t) {map = affine_map<(d0) -> (d0 * 2 + 1)>} : (memref<8xi32>, index) -> i32
      %2 = "arith.addi"(%0, %1) : (i32, i32) -> i32
      "affine.store"(%2, %part, %t) {map = affine_map<(d0) -> (d0)>} : (i32, memref<4xi32>, index) -> ()
      "affine.yield"() : () -> ()
    }) {lowerBoundsMap = affine_map<() -> (0)>, steps = [1], upperBoundsMap = affine_map<() -> (4)>} : () -> ()
    "affine.for"() ({
    ^bb0(%k: index):
      %3 = "affine.load"(%sum, %k) {map = affine_map<(d0) -> (0)>} : (memref<1xi32>, index) -> i32
      %4 = "affine.load"(%part, %k) {map = affine_map<(d0) -> (d0)>} : (memref<4xi32>, index) -> i32
      %5 = "arith.addi"(%3, %4) : (i32, i32) -> i32
      "affine.store"(%5, %sum, %k) {map = affine_map<(d0) -> (0)>} : (i32, memref<1xi32>, index) -> ()
      "affine.yield"() : () -> ()
    }) {lowerBound = affine_map<() -> (0)>, step = 1 : index, upperBound = affine_map<() -> (4)>} : () -> ()
    "func.return"() : () -> ()
  }) {function_type = () -> (), sym_name = "reduction_split"} : () -> ()
}) : () -> ()
