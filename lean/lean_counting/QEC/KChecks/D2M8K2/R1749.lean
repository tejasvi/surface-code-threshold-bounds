import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6996 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6996 = true := by
  decide +kernel

theorem tot6996 : totK PD2M8K2 D2M8K2.t6996 = [0, 176079578073, 456502921067, 251460474156, 22610215694, 0, 0, 0] := by
  decide +kernel

theorem rows6997 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6997 = true := by
  decide +kernel

theorem tot6997 : totK PD2M8K2 D2M8K2.t6997 = [0, 203753272346, 478182203103, 220904638782, 13877082718, 0, 0, 0] := by
  decide +kernel

theorem rows6998 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6998 = true := by
  decide +kernel

theorem tot6998 : totK PD2M8K2 D2M8K2.t6998 = [0, 8130385210, 297051320846, 474196479447, 108569498636, 1268739303, 0, 0] := by
  decide +kernel

theorem rows6999 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6999 = true := by
  decide +kernel

theorem tot6999 : totK PD2M8K2 D2M8K2.t6999 = [0, 0, 210368115228, 481231752538, 183133449696, 7373211019, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
