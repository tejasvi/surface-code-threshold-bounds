import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8660 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8660 = true := by
  decide +kernel

theorem tot8660 : totK PD2M8K2 D2M8K2.t8660 = [0, 34655881336, 340496272351, 441927719633, 76096273869, 1107157161, 0, 0] := by
  decide +kernel

theorem rows8661 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8661 = true := by
  decide +kernel

theorem tot8661 : totK PD2M8K2 D2M8K2.t8661 = [0, 70416564785, 308784054116, 384302417746, 105350988151, 3824247485, 0, 0] := by
  decide +kernel

theorem rows8662 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8662 = true := by
  decide +kernel

theorem tot8662 : totK PD2M8K2 D2M8K2.t8662 = [0, 183750905849, 467644255199, 247482952364, 20128547347, 0, 0, 0] := by
  decide +kernel

theorem rows8663 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8663 = true := by
  decide +kernel

theorem tot8663 : totK PD2M8K2 D2M8K2.t8663 = [0, 181220032959, 472596662747, 236496940648, 12369520860, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
