import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9992 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9992 = true := by
  decide +kernel

theorem tot9992 : totK PD2M8K2 D2M8K2.t9992 = [0, 0, 167592667114, 392773092856, 273299824690, 57470797689, 1409560813, 0] := by
  decide +kernel

theorem rows9993 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9993 = true := by
  decide +kernel

theorem tot9993 : totK PD2M8K2 D2M8K2.t9993 = [0, 0, 189003532693, 467149071913, 216092706048, 12373752831, 0, 0] := by
  decide +kernel

theorem rows9994 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9994 = true := by
  decide +kernel

theorem tot9994 : totK PD2M8K2 D2M8K2.t9994 = [0, 0, 17501539864, 320611543241, 466350628536, 64003112576, 1164319620, 0] := by
  decide +kernel

theorem rows9995 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9995 = true := by
  decide +kernel

theorem tot9995 : totK PD2M8K2 D2M8K2.t9995 = [0, 0, 151083841687, 446156843577, 284361868369, 16966687969, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
