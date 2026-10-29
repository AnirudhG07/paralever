// C[i] = A[i] + B[i] over eight threads, in MLIR *custom* form — the syntax `mlir-opt` prints and
// people write, read by MLIR/Pretty.lean. The generic-form twin is doall-no.mlir, and the two get
// the same verdict: threads write disjoint cells of C, so wfB accepts and par_seq_eq applies.
module {
  memref.global "private" @A : memref<8xi64> = dense<[1, 2, 3, 4, 5, 6, 7, 8]>
  memref.global "private" @B : memref<8xi64> = dense<[10, 20, 30, 40, 50, 60, 70, 80]>
  memref.global "private" @C : memref<8xi64> = dense<0>
  func.func @main() {
    %A = memref.get_global @A : memref<8xi64>
    %B = memref.get_global @B : memref<8xi64>
    %C = memref.get_global @C : memref<8xi64>
    affine.parallel (%i) = (0) to (8) {
      %0 = affine.load %A[%i] : memref<8xi64>
      %1 = affine.load %B[%i] : memref<8xi64>
      %2 = arith.addi %0, %1 : i64
      affine.store %2, %C[%i] : memref<8xi64>
    }
    return
  }
}
