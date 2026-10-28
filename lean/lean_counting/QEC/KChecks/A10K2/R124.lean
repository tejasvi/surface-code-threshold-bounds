import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows496 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t496 = true := by
  decide +kernel

theorem tot496 : totK PA10K2 A10K2.t496 = [0, 0, 762939270719, 2256935048751, 1376150982573, 167876494849, 0, 0, 0, 0] := by
  decide +kernel

theorem rows497 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t497 = true := by
  decide +kernel

theorem tot497 : totK PA10K2 A10K2.t497 = [0, 580375754455, 1878406408278, 1699930739472, 521181292696, 111410273637, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows498 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t498 = true := by
  decide +kernel

theorem tot498 : totK PA10K2 A10K2.t498 = [0, 260421116750, 1430089240074, 2211898258598, 919826889501, 74294261589, 0, 0, 0, 0] := by
  decide +kernel

theorem rows499 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t499 = true := by
  decide +kernel

theorem tot499 : totK PA10K2 A10K2.t499 = [0, 0, 493543323092, 1838013615429, 1881125011216, 506307978326, 31768748853, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
