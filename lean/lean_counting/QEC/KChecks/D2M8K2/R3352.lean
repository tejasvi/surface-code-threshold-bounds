import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13408 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13408 = true := by
  decide +kernel

theorem tot13408 : totK PD2M8K2 D2M8K2.t13408 = [0, 0, 0, 205267503411, 482094254503, 177108149301, 9552748407, 0] := by
  decide +kernel

theorem rows13409 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13409 = true := by
  decide +kernel

theorem tot13409 : totK PD2M8K2 D2M8K2.t13409 = [0, 0, 0, 180253430635, 462139399897, 193645473071, 13409817603, 0] := by
  decide +kernel

theorem rows13410 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13410 = true := by
  decide +kernel

theorem tot13410 : totK PD2M8K2 D2M8K2.t13410 = [0, 0, 0, 0, 334575068138, 418210548199, 73175693717, 1209030869] := by
  decide +kernel

theorem rows13411 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13411 = true := by
  decide +kernel

theorem tot13411 : totK PD2M8K2 D2M8K2.t13411 = [0, 0, 0, 184259277659, 463270043449, 200615042845, 14754600563, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
