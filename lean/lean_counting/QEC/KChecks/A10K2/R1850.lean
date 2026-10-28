import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7400 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7400 = true := by
  decide +kernel

theorem tot7400 : totK PA10K2 A10K2.t7400 = [0, 0, 221672420533, 844368884860, 1579816333733, 1686964590164, 661488420890, 57270499718, 0, 0] := by
  decide +kernel

theorem rows7401 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7401 = true := by
  decide +kernel

theorem tot7401 : totK PA10K2 A10K2.t7401 = [0, 0, 558154890463, 2025850337113, 1997799462938, 468352788167, 26273936808, 0, 0, 0] := by
  decide +kernel

theorem rows7402 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7402 = true := by
  decide +kernel

theorem tot7402 : totK PA10K2 A10K2.t7402 = [0, 0, 0, 703486918051, 2155570550033, 1774264377349, 376036204170, 13576218110, 0, 0] := by
  decide +kernel

theorem rows7403 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7403 = true := by
  decide +kernel

theorem tot7403 : totK PA10K2 A10K2.t7403 = [0, 0, 331085587170, 1477154380753, 2152087623805, 1098848413325, 117333559300, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
