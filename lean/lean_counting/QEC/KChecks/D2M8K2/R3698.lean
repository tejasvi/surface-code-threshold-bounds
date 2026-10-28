import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14792 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14792 = true := by
  decide +kernel

theorem tot14792 : totK PD2M8K2 D2M8K2.t14792 = [0, 169351256650, 435665268693, 275690563069, 30421843854, 0, 0, 0] := by
  decide +kernel

theorem rows14793 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14793 = true := by
  decide +kernel

theorem tot14793 : totK PD2M8K2 D2M8K2.t14793 = [0, 87429419129, 425870162715, 352655796172, 35607994581, 0, 0, 0] := by
  decide +kernel

theorem rows14794 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14794 = true := by
  decide +kernel

theorem tot14794 : totK PD2M8K2 D2M8K2.t14794 = [0, 0, 216785671598, 488654097321, 159574667040, 5218872685, 0, 0] := by
  decide +kernel

theorem rows14795 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14795 = true := by
  decide +kernel

theorem tot14795 : totK PD2M8K2 D2M8K2.t14795 = [0, 171473275786, 423125039523, 290446182204, 44083258551, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
