import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8892 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8892 = true := by
  decide +kernel

theorem tot8892 : totK PD2M8K2 D2M8K2.t8892 = [0, 174464475033, 450835294680, 266575521085, 29033259379, 0, 0, 0] := by
  decide +kernel

theorem rows8893 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8893 = true := by
  decide +kernel

theorem tot8893 : totK PD2M8K2 D2M8K2.t8893 = [0, 133331078670, 436081363858, 304296391755, 32285206004, 0, 0, 0] := by
  decide +kernel

theorem rows8894 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8894 = true := by
  decide +kernel

theorem tot8894 : totK PD2M8K2 D2M8K2.t8894 = [0, 0, 226670243857, 490047482080, 156767873218, 5159868635, 0, 0] := by
  decide +kernel

theorem rows8895 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8895 = true := by
  decide +kernel

theorem tot8895 : totK PD2M8K2 D2M8K2.t8895 = [0, 160940599401, 445714213925, 287840936013, 29733616707, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
