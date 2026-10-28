import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1028 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1028 = true := by
  decide +kernel

theorem tot1028 : totK PA10K2 A10K2.t1028 = [0, 0, 517510347323, 1826453351151, 1952504118520, 651043591555, 49180423016, 0, 0, 0] := by
  decide +kernel

theorem rows1029 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1029 = true := by
  decide +kernel

theorem tot1029 : totK PA10K2 A10K2.t1029 = [0, 0, 400503804029, 1694755765235, 2164342485713, 763761678141, 36984111896, 0, 0, 0] := by
  decide +kernel

theorem rows1030 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1030 = true := by
  decide +kernel

theorem tot1030 : totK PA10K2 A10K2.t1030 = [0, 0, 164038687654, 978130290504, 2086265853729, 1492292471595, 251661600966, 6632180018, 0, 0] := by
  decide +kernel

theorem rows1031 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1031 = true := by
  decide +kernel

theorem tot1031 : totK PA10K2 A10K2.t1031 = [0, 0, 534325474750, 1898008235389, 1918641426887, 529380375778, 31712524204, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
