import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6024 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6024 = true := by
  decide +kernel

theorem tot6024 : totK PA10K2 A10K2.t6024 = [0, 0, 205814172997, 1429922636613, 2136889222564, 763704736646, 58344830985, 0, 0, 0] := by
  decide +kernel

theorem rows6025 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6025 = true := by
  decide +kernel

theorem tot6025 : totK PA10K2 A10K2.t6025 = [315335427872, 992225209073, 892452165915, 459959765739, 924077930173, 868842038205, 207269719194, 6354482628, 0, 0] := by
  decide +kernel

theorem rows6026 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6026 = true := by
  decide +kernel

theorem tot6026 : totK PA10K2 A10K2.t6026 = [520587805808, 1874831253685, 1891278801499, 469971781145, 18560348465, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6027 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6027 = true := by
  decide +kernel

theorem tot6027 : totK PA10K2 A10K2.t6027 = [0, 631896752965, 2047354514639, 1721456044564, 398062458938, 25371180993, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
