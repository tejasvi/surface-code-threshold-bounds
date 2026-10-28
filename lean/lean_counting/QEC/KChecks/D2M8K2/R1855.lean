import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7420 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7420 = true := by
  decide +kernel

theorem tot7420 : totK PD2M8K2 D2M8K2.t7420 = [0, 176929137087, 439809317409, 260960301090, 23498311633, 0, 0, 0] := by
  decide +kernel

theorem rows7421 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7421 = true := by
  decide +kernel

theorem tot7421 : totK PD2M8K2 D2M8K2.t7421 = [0, 54860453394, 385106532778, 406477678837, 50597415074, 0, 0, 0] := by
  decide +kernel

theorem rows7422 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7422 = true := by
  decide +kernel

theorem tot7422 : totK PD2M8K2 D2M8K2.t7422 = [0, 0, 195805839557, 476139851560, 196007612160, 12052611869, 0, 0] := by
  decide +kernel

theorem rows7423 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7423 = true := by
  decide +kernel

theorem tot7423 : totK PD2M8K2 D2M8K2.t7423 = [0, 170621121202, 451792045232, 264200567038, 26930328960, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
