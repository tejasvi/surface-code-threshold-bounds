import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11236 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11236 = true := by
  decide +kernel

theorem tot11236 : totK PD2M8K2 D2M8K2.t11236 = [0, 163133196925, 466412116369, 273781457965, 24200174927, 0, 0, 0] := by
  decide +kernel

theorem rows11237 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11237 = true := by
  decide +kernel

theorem tot11237 : totK PD2M8K2 D2M8K2.t11237 = [0, 0, 178841057584, 449256323222, 247462501033, 25191558099, 0, 0] := by
  decide +kernel

theorem rows11238 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11238 = true := by
  decide +kernel

theorem tot11238 : totK PD2M8K2 D2M8K2.t11238 = [0, 0, 209443916419, 494527768455, 180823036682, 5206224793, 0, 0] := by
  decide +kernel

theorem rows11239 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11239 = true := by
  decide +kernel

theorem tot11239 : totK PD2M8K2 D2M8K2.t11239 = [0, 155525263493, 370708500721, 265314164868, 102721536480, 6524090962, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
