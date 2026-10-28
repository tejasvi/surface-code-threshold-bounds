import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7924 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7924 = true := by
  decide +kernel

theorem tot7924 : totK PD2M8K2 D2M8K2.t7924 = [0, 0, 211097613109, 483179727752, 170710693267, 9482920370, 0, 0] := by
  decide +kernel

theorem rows7925 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7925 = true := by
  decide +kernel

theorem tot7925 : totK PD2M8K2 D2M8K2.t7925 = [0, 175967501358, 447792152713, 240017347726, 44851850588, 2569691499, 0, 0] := by
  decide +kernel

theorem rows7926 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7926 = true := by
  decide +kernel

theorem tot7926 : totK PD2M8K2 D2M8K2.t7926 = [0, 175427876881, 445066702781, 268885988718, 20998392931, 0, 0, 0] := by
  decide +kernel

theorem rows7927 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7927 = true := by
  decide +kernel

theorem tot7927 : totK PD2M8K2 D2M8K2.t7927 = [0, 92932490688, 374886763292, 357189273196, 63845440706, 1096505104, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
