import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7788 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7788 = true := by
  decide +kernel

theorem tot7788 : totK PA10K2 A10K2.t7788 = [0, 119394331873, 974922323102, 2097050931358, 1470154317353, 332063615964, 18595953933, 0, 0, 0] := by
  decide +kernel

theorem rows7789 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7789 = true := by
  decide +kernel

theorem tot7789 : totK PA10K2 A10K2.t7789 = [0, 375251806916, 1467649398881, 2075209423221, 1030740251982, 116994928121, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7790 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7790 = true := by
  decide +kernel

theorem tot7790 : totK PA10K2 A10K2.t7790 = [0, 493242815503, 1901232528214, 2035385946020, 566536007717, 25729529252, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7791 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7791 = true := by
  decide +kernel

theorem tot7791 : totK PA10K2 A10K2.t7791 = [0, 0, 660811496761, 2162753867528, 1866599420451, 346076899726, 6853348008, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
