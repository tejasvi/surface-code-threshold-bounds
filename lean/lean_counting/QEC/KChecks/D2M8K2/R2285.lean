import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9140 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9140 = true := by
  decide +kernel

theorem tot9140 : totK PD2M8K2 D2M8K2.t9140 = [0, 79678872252, 268264043135, 370785827095, 163722573912, 8078182869, 0, 0] := by
  decide +kernel

theorem rows9141 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9141 = true := by
  decide +kernel

theorem tot9141 : totK PD2M8K2 D2M8K2.t9141 = [0, 174698991191, 447811628298, 265477373659, 25637699251, 0, 0, 0] := by
  decide +kernel

theorem rows9142 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9142 = true := by
  decide +kernel

theorem tot9142 : totK PD2M8K2 D2M8K2.t9142 = [0, 71604467339, 339034847814, 403919712876, 79227241199, 1164319620, 0, 0] := by
  decide +kernel

theorem rows9143 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9143 = true := by
  decide +kernel

theorem tot9143 : totK PD2M8K2 D2M8K2.t9143 = [0, 84525017608, 308883191127, 389971000881, 110496819655, 4008488258, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
