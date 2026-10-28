import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1180 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1180 = true := by
  decide +kernel

theorem tot1180 : totK PA10K2 A10K2.t1180 = [0, 0, 0, 764681965371, 2236449361000, 1595489086596, 270958372054, 6904928264, 0, 0] := by
  decide +kernel

theorem rows1181 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1181 = true := by
  decide +kernel

theorem tot1181 : totK PA10K2 A10K2.t1181 = [0, 0, 476447417375, 1744211663698, 2050162537241, 782686581437, 62237202217, 0, 0, 0] := by
  decide +kernel

theorem rows1182 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1182 = true := by
  decide +kernel

theorem tot1182 : totK PA10K2 A10K2.t1182 = [0, 0, 147905126895, 1015084173279, 2220955776186, 1495836780822, 172807740233, 0, 0, 0] := by
  decide +kernel

theorem rows1183 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1183 = true := by
  decide +kernel

theorem tot1183 : totK PA10K2 A10K2.t1183 = [0, 0, 522065584750, 1887411156630, 1978578183642, 544154447418, 19375727937, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
