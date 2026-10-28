import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5016 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5016 = true := by
  decide +kernel

theorem tot5016 : totK PD2M8K2 D2M8K2.t5016 = [0, 0, 302824990852, 524374634176, 90393464207, 0, 0, 0] := by
  decide +kernel

theorem rows5017 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5017 = true := by
  decide +kernel

theorem tot5017 : totK PD2M8K2 D2M8K2.t5017 = [0, 153291077650, 379920747264, 281582050204, 88186786659, 3884009855, 0, 0] := by
  decide +kernel

theorem rows5018 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5018 = true := by
  decide +kernel

theorem tot5018 : totK PD2M8K2 D2M8K2.t5018 = [0, 176734205922, 457409885129, 265936952173, 19348741913, 0, 0, 0] := by
  decide +kernel

theorem rows5019 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5019 = true := by
  decide +kernel

theorem tot5019 : totK PD2M8K2 D2M8K2.t5019 = [0, 0, 281248383746, 507610705287, 112300638977, 1268739303, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
