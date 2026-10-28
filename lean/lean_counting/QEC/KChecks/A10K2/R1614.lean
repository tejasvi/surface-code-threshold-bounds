import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6456 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6456 = true := by
  decide +kernel

theorem tot6456 : totK PA10K2 A10K2.t6456 = [0, 0, 359718672936, 1570485231086, 2086796335452, 840417852290, 75177836158, 0, 0, 0] := by
  decide +kernel

theorem rows6457 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6457 = true := by
  decide +kernel

theorem tot6457 : totK PA10K2 A10K2.t6457 = [0, 0, 519984968088, 1905341145407, 1971195819549, 479343958711, 12558985842, 0, 0, 0] := by
  decide +kernel

theorem rows6458 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6458 = true := by
  decide +kernel

theorem tot6458 : totK PA10K2 A10K2.t6458 = [0, 0, 0, 766055886076, 2180483544402, 1539050894622, 269930207871, 7151180950, 0, 0] := by
  decide +kernel

theorem rows6459 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6459 = true := by
  decide +kernel

theorem tot6459 : totK PA10K2 A10K2.t6459 = [0, 0, 615151998610, 1931907514570, 1701765844899, 464732787982, 30107499662, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
