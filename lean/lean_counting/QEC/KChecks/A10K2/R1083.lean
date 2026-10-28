import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4332 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4332 = true := by
  decide +kernel

theorem tot4332 : totK PA10K2 A10K2.t4332 = [0, 0, 586772247909, 2019506239143, 1908461152029, 446959529337, 25574931378, 0, 0, 0] := by
  decide +kernel

theorem rows4333 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4333 = true := by
  decide +kernel

theorem tot4333 : totK PA10K2 A10K2.t4333 = [0, 0, 0, 760981747048, 2234553538435, 1671120430424, 286419054556, 6853348008, 0, 0] := by
  decide +kernel

theorem rows4334 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4334 = true := by
  decide +kernel

theorem tot4334 : totK PA10K2 A10K2.t4334 = [0, 0, 0, 572546642247, 1999049241818, 1802912688344, 469642082096, 37743864755, 0, 0] := by
  decide +kernel

theorem rows4335 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4335 = true := by
  decide +kernel

theorem tot4335 : totK PA10K2 A10K2.t4335 = [0, 0, 0, 536972639171, 1872984064639, 1797425267590, 424828474186, 16247670858, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
