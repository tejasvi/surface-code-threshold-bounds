import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14192 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14192 = true := by
  decide +kernel

theorem tot14192 : totK PD2M8K2 D2M8K2.t14192 = [190821610167, 455766850706, 221424886007, 16930344841, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14193 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14193 = true := by
  decide +kernel

theorem tot14193 : totK PD2M8K2 D2M8K2.t14193 = [113893176177, 423637566341, 314023904279, 29579823443, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14194 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14194 = true := by
  decide +kernel

theorem tot14194 : totK PD2M8K2 D2M8K2.t14194 = [0, 269666162963, 503389518723, 110156364733, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows14195 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14195 = true := by
  decide +kernel

theorem tot14195 : totK PD2M8K2 D2M8K2.t14195 = [171798127067, 422046399750, 303712796500, 39193325545, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
