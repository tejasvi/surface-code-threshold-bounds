import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows956 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t956 = true := by
  decide +kernel

theorem tot956 : totK PA10K2 A10K2.t956 = [0, 451837475987, 1651375498966, 1990414825756, 772484897446, 74012258383, 0, 0, 0, 0] := by
  decide +kernel

theorem rows957 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t957 = true := by
  decide +kernel

theorem tot957 : totK PA10K2 A10K2.t957 = [0, 289185646877, 1463135044961, 2103365751756, 828232743126, 51325750866, 0, 0, 0, 0] := by
  decide +kernel

theorem rows958 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t958 = true := by
  decide +kernel

theorem tot958 : totK PA10K2 A10K2.t958 = [0, 0, 719319833502, 2155449932660, 1522227563363, 262094519341, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows959 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t959 = true := by
  decide +kernel

theorem tot959 : totK PA10K2 A10K2.t959 = [0, 0, 485162519432, 1848351761456, 1973031724584, 512429867104, 31609816132, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
