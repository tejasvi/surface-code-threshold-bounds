import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2648 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2648 = true := by
  decide +kernel

theorem tot2648 : totK PD2M8K2 D2M8K2.t2648 = [0, 0, 59162266578, 394232130927, 405932144608, 45082216171, 0, 0] := by
  decide +kernel

theorem rows2649 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2649 = true := by
  decide +kernel

theorem tot2649 : totK PD2M8K2 D2M8K2.t2649 = [0, 0, 28151026966, 215918138297, 467738247884, 143061749457, 5067863418, 0] := by
  decide +kernel

theorem rows2650 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2650 = true := by
  decide +kernel

theorem tot2650 : totK PD2M8K2 D2M8K2.t2650 = [0, 0, 196326648642, 472530460247, 225147915189, 21890168488, 0, 0] := by
  decide +kernel

theorem rows2651 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2651 = true := by
  decide +kernel

theorem tot2651 : totK PD2M8K2 D2M8K2.t2651 = [0, 0, 188950952008, 471721619816, 219343564513, 9121934200, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
