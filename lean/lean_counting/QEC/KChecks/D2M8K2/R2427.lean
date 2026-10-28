import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9708 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9708 = true := by
  decide +kernel

theorem tot9708 : totK PD2M8K2 D2M8K2.t9708 = [0, 160406366033, 464321022456, 264444358127, 22744200387, 0, 0, 0] := by
  decide +kernel

theorem rows9709 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9709 = true := by
  decide +kernel

theorem tot9709 : totK PD2M8K2 D2M8K2.t9709 = [0, 182261201038, 478984593651, 248450256897, 13922086798, 0, 0, 0] := by
  decide +kernel

theorem rows9710 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9710 = true := by
  decide +kernel

theorem tot9710 : totK PD2M8K2 D2M8K2.t9710 = [0, 0, 266752271966, 499305353707, 119390139993, 1268739303, 0, 0] := by
  decide +kernel

theorem rows9711 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9711 = true := by
  decide +kernel

theorem tot9711 : totK PD2M8K2 D2M8K2.t9711 = [0, 0, 199853459484, 484888684205, 192456324793, 8601127387, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
