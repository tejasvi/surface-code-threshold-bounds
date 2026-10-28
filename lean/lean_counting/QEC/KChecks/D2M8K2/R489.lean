import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1956 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1956 = true := by
  decide +kernel

theorem tot1956 : totK PD2M8K2 D2M8K2.t1956 = [0, 68459858781, 298596826343, 412969587560, 111985663969, 3884009855, 0, 0] := by
  decide +kernel

theorem rows1957 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1957 = true := by
  decide +kernel

theorem tot1957 : totK PD2M8K2 D2M8K2.t1957 = [0, 167005957146, 456590285788, 253755805895, 20816958596, 0, 0, 0] := by
  decide +kernel

theorem rows1958 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1958 = true := by
  decide +kernel

theorem tot1958 : totK PD2M8K2 D2M8K2.t1958 = [0, 179476509406, 463368160813, 246987747522, 18171145108, 0, 0, 0] := by
  decide +kernel

theorem rows1959 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1959 = true := by
  decide +kernel

theorem tot1959 : totK PD2M8K2 D2M8K2.t1959 = [0, 0, 271618997438, 497757569734, 121401072803, 1268739303, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
