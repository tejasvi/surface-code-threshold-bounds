import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12648 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12648 = true := by
  decide +kernel

theorem tot12648 : totK PD2M8K2 D2M8K2.t12648 = [0, 0, 0, 19196702418, 348434953177, 414175023088, 72931432756, 1369150432] := by
  decide +kernel

theorem rows12649 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12649 = true := by
  decide +kernel

theorem tot12649 : totK PD2M8K2 D2M8K2.t12649 = [0, 0, 0, 145177583298, 459393745869, 244877125907, 17813760226, 0] := by
  decide +kernel

theorem rows12650 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12650 = true := by
  decide +kernel

theorem tot12650 : totK PD2M8K2 D2M8K2.t12650 = [0, 0, 0, 207402003606, 471591958270, 173417714405, 12082697338, 0] := by
  decide +kernel

theorem rows12651 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12651 = true := by
  decide +kernel

theorem tot12651 : totK PD2M8K2 D2M8K2.t12651 = [0, 0, 0, 289039021266, 500012348265, 113001637433, 1369549770, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
