import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7120 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7120 = true := by
  decide +kernel

theorem tot7120 : totK PD2M8K2 D2M8K2.t7120 = [0, 0, 286006198425, 497386568987, 110579678628, 1369150432, 0, 0] := by
  decide +kernel

theorem rows7121 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7121 = true := by
  decide +kernel

theorem tot7121 : totK PD2M8K2 D2M8K2.t7121 = [0, 86950764009, 392529226735, 381382251444, 41721100382, 0, 0, 0] := by
  decide +kernel

theorem rows7122 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7122 = true := by
  decide +kernel

theorem tot7122 : totK PD2M8K2 D2M8K2.t7122 = [0, 166256248390, 453101848913, 273644433634, 26982777574, 0, 0, 0] := by
  decide +kernel

theorem rows7123 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7123 = true := by
  decide +kernel

theorem tot7123 : totK PD2M8K2 D2M8K2.t7123 = [0, 168874068918, 459798381858, 247114969093, 16989259913, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
