// a floating-point stencil: B[i] := 0.5*A[i] + 0.25*A[i+1] + 0.25*A[i+2], over f64.
// Neighbouring threads read windows overlapping in two cells while their writes stay
// disjoint singletons — the case separating conjunction rejects and Bernstein accepts.
// The element type changes the values and not one address, so the verdict is the verdict of
// the integer twin. The results are not integral, which is the point: the Int lowering
// truncates each term and MLIR/Eval.lean does not.
// Expected verdict: race-free. Expected reference result: B[0] = 7/4.
"builtin.module"() ({
  "memref.global"() {sym_name = "A", type = memref<8xf64>, initial_value = dense<[1, 2, 3, 4, 5, 6, 7, 8]>} : () -> ()
  "func.func"() ({
    %A = "memref.get_global"() {name = @A} : () -> memref<8xf64>
    %B = "memref.alloc"() : () -> memref<8xf64>
    "affine.parallel"() ({
    ^bb0(%i: index):
      %h = "arith.constant"() {value = 0.5 : f64} : () -> f64
      %q = "arith.constant"() {value = 0.25 : f64} : () -> f64
      %0 = "affine.load"(%A, %i) {map = affine_map<(d0) -> (d0)>} : (memref<8xf64>, index) -> f64
      %1 = "affine.load"(%A, %i) {map = affine_map<(d0) -> (d0 + 1)>} : (memref<8xf64>, index) -> f64
      %2 = "affine.load"(%A, %i) {map = affine_map<(d0) -> (d0 + 2)>} : (memref<8xf64>, index) -> f64
      %3 = "arith.mulf"(%h, %0) : (f64, f64) -> f64
      %4 = "arith.mulf"(%q, %1) : (f64, f64) -> f64
      %5 = "arith.mulf"(%q, %2) : (f64, f64) -> f64
      %6 = "arith.addf"(%3, %4) : (f64, f64) -> f64
      %7 = "arith.addf"(%6, %5) : (f64, f64) -> f64
      "affine.store"(%7, %B, %i) {map = affine_map<(d0) -> (d0)>} : (f64, memref<8xf64>, index) -> ()
      "affine.yield"() : () -> ()
    }) {lowerBoundsMap = affine_map<() -> (0)>, steps = [1], upperBoundsMap = affine_map<() -> (6)>} : () -> ()
    "func.return"() : () -> ()
  }) {function_type = () -> (), sym_name = "stencil"} : () -> ()
}) : () -> ()
