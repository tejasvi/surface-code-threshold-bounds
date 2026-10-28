import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6556 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6556 = true := by
  decide +kernel

theorem tot6556 : totK PA10K2 A10K2.t6556 = [0, 461452330429, 1638097486602, 1820001895980, 765217026574, 87165371873, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6557 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6557 = true := by
  decide +kernel

theorem tot6557 : totK PA10K2 A10K2.t6557 = [0, 289345254879, 1471384546049, 2132399387669, 795245512498, 53767481017, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6558 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6558 = true := by
  decide +kernel

theorem tot6558 : totK PA10K2 A10K2.t6558 = [0, 298812713684, 1237958321912, 1848740038567, 1157155216041, 221302407274, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows6559 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6559 = true := by
  decide +kernel

theorem tot6559 : totK PA10K2 A10K2.t6559 = [0, 296343083234, 1477714453366, 2240631338488, 991789091504, 82803045539, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
