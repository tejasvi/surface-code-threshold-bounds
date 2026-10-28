import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14980 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14980 = true := by
  decide +kernel

theorem tot14980 : totK PD2M8K2 D2M8K2.t14980 = [0, 165290289616, 465647375023, 265808246978, 16227148200, 0, 0, 0] := by
  decide +kernel

theorem rows14981 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14981 = true := by
  decide +kernel

theorem tot14981 : totK PD2M8K2 D2M8K2.t14981 = [0, 0, 271833433066, 500160494308, 121079222238, 1268739303, 0, 0] := by
  decide +kernel

theorem rows14982 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14982 = true := by
  decide +kernel

theorem tot14982 : totK PD2M8K2 D2M8K2.t14982 = [0, 0, 186701211881, 479626708873, 206421708115, 8601051048, 0, 0] := by
  decide +kernel

theorem rows14983 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14983 = true := by
  decide +kernel

theorem tot14983 : totK PD2M8K2 D2M8K2.t14983 = [0, 0, 176649873492, 470914453554, 219600962686, 14629206711, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
