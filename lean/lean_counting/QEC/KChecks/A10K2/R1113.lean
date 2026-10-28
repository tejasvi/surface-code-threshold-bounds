import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4452 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4452 = true := by
  decide +kernel

theorem tot4452 : totK PA10K2 A10K2.t4452 = [0, 736479923321, 2119411159845, 1666728655840, 377541663694, 25734533292, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4453 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4453 = true := by
  decide +kernel

theorem tot4453 : totK PA10K2 A10K2.t4453 = [152063379648, 946315613826, 1944477752425, 1434004937213, 246615848017, 6034215561, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4454 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4454 = true := by
  decide +kernel

theorem tot4454 : totK PA10K2 A10K2.t4454 = [493772440584, 1699416352290, 1870179097094, 640309716715, 52133613764, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4455 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4455 = true := by
  decide +kernel

theorem tot4455 : totK PA10K2 A10K2.t4455 = [82274800672, 1162141126708, 2270226742056, 1057103678340, 95172942946, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
