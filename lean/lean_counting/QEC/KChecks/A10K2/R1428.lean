import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5712 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5712 = true := by
  decide +kernel

theorem tot5712 : totK PA10K2 A10K2.t5712 = [0, 0, 500363765791, 1852811863733, 1902032625823, 513134841668, 31608797364, 0, 0, 0] := by
  decide +kernel

theorem rows5713 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5713 = true := by
  decide +kernel

theorem tot5713 : totK PA10K2 A10K2.t5713 = [0, 0, 110080449477, 1274513262263, 2355224912970, 916719991915, 65326404304, 0, 0, 0] := by
  decide +kernel

theorem rows5714 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5714 = true := by
  decide +kernel

theorem tot5714 : totK PA10K2 A10K2.t5714 = [0, 0, 438853063276, 1447843298015, 1754765265582, 898403568930, 153851967938, 5546304973, 0, 0] := by
  decide +kernel

theorem rows5715 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5715 = true := by
  decide +kernel

theorem tot5715 : totK PA10K2 A10K2.t5715 = [0, 449259150676, 1427782561962, 1694077129905, 1001540208874, 284861969408, 12645167858, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
