import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1960 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1960 = true := by
  decide +kernel

theorem tot1960 : totK PA10K2 A10K2.t1960 = [0, 371335780827, 1621002585995, 2139398843315, 865414687597, 78639266415, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1961 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1961 = true := by
  decide +kernel

theorem tot1961 : totK PA10K2 A10K2.t1961 = [0, 0, 553984669891, 1916306245468, 1863033122716, 489934310822, 31768748853, 0, 0, 0] := by
  decide +kernel

theorem rows1962 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1962 = true := by
  decide +kernel

theorem tot1962 : totK PA10K2 A10K2.t1962 = [0, 329492980431, 1420039528318, 2102230134502, 1010581145876, 99385614667, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1963 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1963 = true := by
  decide +kernel

theorem tot1963 : totK PA10K2 A10K2.t1963 = [0, 494825702548, 1845973837290, 2024986634413, 605365696361, 42498263094, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
