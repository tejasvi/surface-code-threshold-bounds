import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8276 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8276 = true := by
  decide +kernel

theorem tot8276 : totK PD2M8K2 D2M8K2.t8276 = [0, 0, 311393998684, 464077769083, 75441900428, 1021600638, 0, 0] := by
  decide +kernel

theorem rows8277 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8277 = true := by
  decide +kernel

theorem tot8277 : totK PD2M8K2 D2M8K2.t8277 = [0, 89355778958, 349487761184, 333762696199, 76305736775, 3552795014, 0, 0] := by
  decide +kernel

theorem rows8278 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8278 = true := by
  decide +kernel

theorem tot8278 : totK PD2M8K2 D2M8K2.t8278 = [0, 187596639056, 453025096539, 245402784259, 24114235687, 0, 0, 0] := by
  decide +kernel

theorem rows8279 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8279 = true := by
  decide +kernel

theorem tot8279 : totK PD2M8K2 D2M8K2.t8279 = [72314505312, 221589237522, 371668407952, 219636827300, 17476474534, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
