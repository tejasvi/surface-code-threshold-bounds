import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14688 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14688 = true := by
  decide +kernel

theorem tot14688 : totK PD2M8K2 D2M8K2.t14688 = [0, 189449512601, 477258889097, 225305451698, 15652015245, 0, 0, 0] := by
  decide +kernel

theorem rows14689 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14689 = true := by
  decide +kernel

theorem tot14689 : totK PD2M8K2 D2M8K2.t14689 = [0, 70166284074, 347973366078, 380703362395, 104935957959, 8332571741, 0, 0] := by
  decide +kernel

theorem rows14690 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14690 = true := by
  decide +kernel

theorem tot14690 : totK PD2M8K2 D2M8K2.t14690 = [0, 0, 243835713174, 489690936254, 172967610547, 5324200119, 0, 0] := by
  decide +kernel

theorem rows14691 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14691 = true := by
  decide +kernel

theorem tot14691 : totK PD2M8K2 D2M8K2.t14691 = [0, 142949208276, 371668512534, 296692573013, 85355529470, 1409560813, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
