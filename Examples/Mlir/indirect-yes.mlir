// indirect access: A[Idx[i]] := i, run in parallel. The subscript is a loaded value, so it
// is not affine and `memref.store` is the only op that can carry it. Paralever's footprint
// for a computed address is the whole array, so the threads are rejected whatever Idx holds.
// Expected verdict: racy — and conservatively so, which the corpus report records.
"builtin.module"() ({
  "func.func"() ({
  ^bb0(%Idx: memref<4xi32>, %A: memref<4xi32>):
    "affine.parallel"() ({
    ^bb0(%i: index):
      %0 = "affine.load"(%Idx, %i) {map = affine_map<(d0) -> (d0)>} : (memref<4xi32>, index) -> i32
      %1 = "arith.index_cast"(%0) : (i32) -> index
      %2 = "arith.index_cast"(%i) : (index) -> i32
      "memref.store"(%2, %A, %1) : (i32, memref<4xi32>, index) -> ()
      "affine.yield"() : () -> ()
    }) {lowerBoundsMap = affine_map<() -> (0)>, steps = [1], upperBoundsMap = affine_map<() -> (4)>} : () -> ()
    "func.return"() : () -> ()
  }) {function_type = (memref<4xi32>, memref<4xi32>) -> (), sym_name = "indirect"} : () -> ()
}) : () -> ()
