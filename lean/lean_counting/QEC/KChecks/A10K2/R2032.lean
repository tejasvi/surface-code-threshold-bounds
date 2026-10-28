import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8128 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8128 = true := by
  decide +kernel

theorem tot8128 : totK PA10K2 A10K2.t8128 = [0, 0, 0, 435172828435, 1616453006652, 1946548339617, 776539828015, 68086446142, 0, 0] := by
  decide +kernel

theorem rows8129 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8129 = true := by
  decide +kernel

theorem tot8129 : totK PA10K2 A10K2.t8129 = [0, 0, 0, 374773419119, 1658477670181, 2082944687076, 735056839278, 53808929478, 0, 0] := by
  decide +kernel

theorem rows8130 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8130 = true := by
  decide +kernel

theorem tot8130 : totK PA10K2 A10K2.t8130 = [0, 0, 0, 0, 681650828730, 2064074100322, 1581334344057, 295815323363, 12696458652, 0] := by
  decide +kernel

theorem rows8131 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8131 = true := by
  decide +kernel

theorem tot8131 : totK PA10K2 A10K2.t8131 = [0, 0, 0, 443742495885, 1718839943144, 1914324397479, 700151154326, 51310514611, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
