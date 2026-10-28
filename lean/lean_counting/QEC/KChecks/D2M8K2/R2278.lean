import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9112 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9112 = true := by
  decide +kernel

theorem tot9112 : totK PD2M8K2 D2M8K2.t9112 = [0, 180641555456, 465783078200, 250732936122, 22717815589, 0, 0, 0] := by
  decide +kernel

theorem rows9113 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9113 = true := by
  decide +kernel

theorem tot9113 : totK PD2M8K2 D2M8K2.t9113 = [0, 160808681271, 472568794668, 255660482882, 13779823240, 0, 0, 0] := by
  decide +kernel

theorem rows9114 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9114 = true := by
  decide +kernel

theorem tot9114 : totK PD2M8K2 D2M8K2.t9114 = [0, 0, 281209430174, 498830595903, 111834736082, 1198073392, 0, 0] := by
  decide +kernel

theorem rows9115 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9115 = true := by
  decide +kernel

theorem tot9115 : totK PD2M8K2 D2M8K2.t9115 = [0, 18530029189, 195000397964, 457330904056, 194160010317, 12052611869, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
