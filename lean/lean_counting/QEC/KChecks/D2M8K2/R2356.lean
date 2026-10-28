import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9424 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9424 = true := by
  decide +kernel

theorem tot9424 : totK PD2M8K2 D2M8K2.t9424 = [0, 180758428870, 485298235863, 236601932542, 12526962336, 0, 0, 0] := by
  decide +kernel

theorem rows9425 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9425 = true := by
  decide +kernel

theorem tot9425 : totK PD2M8K2 D2M8K2.t9425 = [0, 0, 276859262991, 520415935239, 101912449421, 1096505104, 0, 0] := by
  decide +kernel

theorem rows9426 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9426 = true := by
  decide +kernel

theorem tot9426 : totK PD2M8K2 D2M8K2.t9426 = [0, 0, 231797336869, 495893513291, 160352241361, 5253830308, 0, 0] := by
  decide +kernel

theorem rows9427 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9427 = true := by
  decide +kernel

theorem tot9427 : totK PD2M8K2 D2M8K2.t9427 = [0, 0, 173350020978, 451692824429, 204894763263, 16680312209, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
