// The missing-reduction bug in custom form: every thread of the affine.parallel accumulates into
// S[0], so eight threads read and write one cell. wfB refuses it, a schedule reaches wrong, and
// `paralever race` prints that schedule. The generic-form twin is reduction-yes.mlir.
module {
  memref.global "private" @A : memref<8xi64> = dense<[1, 2, 3, 4, 5, 6, 7, 8]>
  memref.global "private" @S : memref<1xi64> = dense<0>
  func.func @main() {
    %A = memref.get_global @A : memref<8xi64>
    %S = memref.get_global @S : memref<1xi64>
    affine.parallel (%i) = (0) to (8) {
      %0 = affine.load %A[%i] : memref<8xi64>
      %1 = affine.load %S[0] : memref<1xi64>
      %2 = arith.addi %1, %0 : i64
      affine.store %2, %S[0] : memref<1xi64>
    }
    return
  }
}
