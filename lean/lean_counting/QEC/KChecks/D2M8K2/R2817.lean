import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11268 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11268 = true := by
  decide +kernel

theorem tot11268 : totK PD2M8K2 D2M8K2.t11268 = [159319719328, 459107926965, 263624226430, 18668316587, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11269 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11269 = true := by
  decide +kernel

theorem tot11269 : totK PD2M8K2 D2M8K2.t11269 = [0, 284650145063, 515991204448, 105497860784, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows11270 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11270 = true := by
  decide +kernel

theorem tot11270 : totK PD2M8K2 D2M8K2.t11270 = [134017194337, 360628475526, 305194185442, 91319381394, 3884009855, 0, 0, 0] := by
  decide +kernel

theorem rows11271 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11271 = true := by
  decide +kernel

theorem tot11271 : totK PD2M8K2 D2M8K2.t11271 = [162121104403, 440834094558, 287297126849, 30247476123, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
