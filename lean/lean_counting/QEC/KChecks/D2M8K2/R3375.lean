import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13500 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13500 = true := by
  decide +kernel

theorem tot13500 : totK PD2M8K2 D2M8K2.t13500 = [0, 0, 0, 171949391705, 451417957255, 240265536342, 18109095603, 0] := by
  decide +kernel

theorem rows13501 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13501 = true := by
  decide +kernel

theorem tot13501 : totK PD2M8K2 D2M8K2.t13501 = [0, 0, 0, 92324975456, 358296237199, 344561734893, 68878095716, 1095107716] := by
  decide +kernel

theorem rows13502 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13502 = true := by
  decide +kernel

theorem tot13502 : totK PD2M8K2 D2M8K2.t13502 = [0, 0, 0, 0, 302510027739, 473420372064, 95377783399, 1067409660] := by
  decide +kernel

theorem rows13503 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13503 = true := by
  decide +kernel

theorem tot13503 : totK PD2M8K2 D2M8K2.t13503 = [186677387228, 459373490871, 202050743940, 9852138406, 0, 20251497215, 25709098530, 2814597007] := by
  decide +kernel

end QECKChecks.D2M8K2
