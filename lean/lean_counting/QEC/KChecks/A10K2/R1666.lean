import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6664 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6664 = true := by
  decide +kernel

theorem tot6664 : totK PA10K2 A10K2.t6664 = [0, 447826142624, 1815654654113, 1967434692637, 503620184235, 31090071023, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6665 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6665 = true := by
  decide +kernel

theorem tot6665 : totK PA10K2 A10K2.t6665 = [263701001044, 633312963203, 784446508309, 1560303142730, 1143127978259, 233158376432, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows6666 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6666 = true := by
  decide +kernel

theorem tot6666 : totK PA10K2 A10K2.t6666 = [514692062441, 1884134081156, 1934108928690, 526990198433, 31989350221, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6667 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6667 = true := by
  decide +kernel

theorem tot6667 : totK PA10K2 A10K2.t6667 = [0, 743090057373, 2125600885244, 1650898246938, 382481315770, 25351274858, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
