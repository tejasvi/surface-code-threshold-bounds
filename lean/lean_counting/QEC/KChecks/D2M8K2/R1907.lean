import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7628 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7628 = true := by
  decide +kernel

theorem tot7628 : totK PD2M8K2 D2M8K2.t7628 = [0, 161889032206, 449957820278, 282184612493, 23746959693, 0, 0, 0] := by
  decide +kernel

theorem rows7629 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7629 = true := by
  decide +kernel

theorem tot7629 : totK PD2M8K2 D2M8K2.t7629 = [0, 0, 225538770913, 492371269781, 154669687004, 5455647540, 0, 0] := by
  decide +kernel

theorem rows7630 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7630 = true := by
  decide +kernel

theorem tot7630 : totK PD2M8K2 D2M8K2.t7630 = [0, 175988942929, 447485081250, 263214848290, 34925915888, 0, 0, 0] := by
  decide +kernel

theorem rows7631 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7631 = true := by
  decide +kernel

theorem tot7631 : totK PD2M8K2 D2M8K2.t7631 = [0, 172091788327, 444070523484, 274945242435, 29931978176, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
