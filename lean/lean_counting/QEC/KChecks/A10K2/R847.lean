import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3388 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3388 = true := by
  decide +kernel

theorem tot3388 : totK PA10K2 A10K2.t3388 = [0, 0, 0, 480702974008, 1807452806647, 2045609203477, 680710221775, 42634117289, 0, 0] := by
  decide +kernel

theorem rows3389 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3389 = true := by
  decide +kernel

theorem tot3389 : totK PA10K2 A10K2.t3389 = [0, 0, 0, 103234562172, 951877356618, 2132095445163, 1482911150134, 218933437080, 6439430839, 0] := by
  decide +kernel

theorem rows3390 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3390 = true := by
  decide +kernel

theorem tot3390 : totK PA10K2 A10K2.t3390 = [0, 0, 0, 535843583423, 1883565804812, 1948171259697, 509897278047, 18609036708, 0, 0] := by
  decide +kernel

theorem rows3391 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3391 = true := by
  decide +kernel

theorem tot3391 : totK PA10K2 A10K2.t3391 = [0, 0, 0, 225901357694, 1300657154786, 2215403399674, 1169907365331, 117667960592, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
