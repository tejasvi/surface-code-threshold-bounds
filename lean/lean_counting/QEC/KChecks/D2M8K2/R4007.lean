import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16028 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16028 = true := by
  decide +kernel

theorem tot16028 : totK PD2M8K2 D2M8K2.t16028 = [0, 0, 205556929783, 478863160775, 189497171416, 9786135328, 0, 0] := by
  decide +kernel

theorem rows16029 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16029 = true := by
  decide +kernel

theorem tot16029 : totK PD2M8K2 D2M8K2.t16029 = [0, 0, 86073074144, 378885815371, 344437752472, 54361124032, 1310517177, 0] := by
  decide +kernel

theorem rows16030 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16030 = true := by
  decide +kernel

theorem tot16030 : totK PD2M8K2 D2M8K2.t16030 = [0, 0, 74020660143, 396042267914, 401700643954, 28243316725, 0, 0] := by
  decide +kernel

theorem rows16031 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16031 = true := by
  decide +kernel

theorem tot16031 : totK PD2M8K2 D2M8K2.t16031 = [0, 0, 180974439091, 450720786675, 266245005105, 30595136807, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
