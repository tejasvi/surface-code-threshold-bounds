import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7284 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7284 = true := by
  decide +kernel

theorem tot7284 : totK PA10K2 A10K2.t7284 = [0, 0, 554312439883, 1845535530282, 1937381113564, 597011596087, 33480676086, 0, 0, 0] := by
  decide +kernel

theorem rows7285 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7285 = true := by
  decide +kernel

theorem tot7285 : totK PA10K2 A10K2.t7285 = [0, 0, 46039240014, 890632475747, 2211349886119, 1599964607964, 269792675276, 6772895877, 0, 0] := by
  decide +kernel

theorem rows7286 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7286 = true := by
  decide +kernel

theorem tot7286 : totK PA10K2 A10K2.t7286 = [0, 0, 0, 531935643421, 1976875996281, 2023163965258, 498203056061, 18736574845, 0, 0] := by
  decide +kernel

theorem rows7287 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7287 = true := by
  decide +kernel

theorem tot7287 : totK PA10K2 A10K2.t7287 = [0, 0, 0, 485018482987, 1748429870617, 1950517728051, 630262291830, 49321567661, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
