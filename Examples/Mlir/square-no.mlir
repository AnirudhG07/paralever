// A[i] := A[i] * A[i] over three threads, in MLIR custom form. Deliberately the smallest module
// that still says everything: one buffer, one affine.parallel, one arith op. Thread i reads and
// writes only A[i], so the footprints are pairwise independent and wfB accepts.
memref.global "private" @A : memref<3xi64> = dense<[2, 3, 4]>
func.func @main() {
  %A = memref.get_global @A : memref<3xi64>
  affine.parallel (%i) = (0) to (3) {
    %0 = affine.load %A[%i] : memref<3xi64>
    %1 = arith.muli %0, %0 : i64
    affine.store %1, %A[%i] : memref<3xi64>
  }
  return
}
