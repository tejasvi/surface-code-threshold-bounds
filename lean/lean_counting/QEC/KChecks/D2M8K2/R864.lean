import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3456 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3456 = true := by
  decide +kernel

theorem tot3456 : totK PD2M8K2 D2M8K2.t3456 = [0, 181484076332, 459440080743, 260692320511, 23032220827, 0, 0, 0] := by
  decide +kernel

theorem rows3457 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3457 = true := by
  decide +kernel

theorem tot3457 : totK PD2M8K2 D2M8K2.t3457 = [0, 166310149807, 461004728989, 256900459858, 15983050630, 0, 0, 0] := by
  decide +kernel

theorem rows3458 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3458 = true := by
  decide +kernel

theorem tot3458 : totK PD2M8K2 D2M8K2.t3458 = [0, 0, 272606700941, 485331846629, 126172206701, 4009909289, 0, 0] := by
  decide +kernel

theorem rows3459 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3459 = true := by
  decide +kernel

theorem tot3459 : totK PD2M8K2 D2M8K2.t3459 = [0, 85074305833, 339324458096, 384733744187, 79216646732, 1149959346, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
