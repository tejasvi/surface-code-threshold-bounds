import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8848 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8848 = true := by
  decide +kernel

theorem tot8848 : totK PD2M8K2 D2M8K2.t8848 = [90840904916, 384051215113, 355851702575, 57121751076, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows8849 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8849 = true := by
  decide +kernel

theorem tot8849 : totK PD2M8K2 D2M8K2.t8849 = [0, 317825154582, 503113019132, 81020163813, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8850 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8850 = true := by
  decide +kernel

theorem tot8850 : totK PD2M8K2 D2M8K2.t8850 = [157174987332, 385523684383, 273602337055, 84445274812, 3884009855, 0, 0, 0] := by
  decide +kernel

theorem rows8851 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8851 = true := by
  decide +kernel

theorem tot8851 : totK PD2M8K2 D2M8K2.t8851 = [164257180446, 435803044493, 262373555883, 24053966618, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
