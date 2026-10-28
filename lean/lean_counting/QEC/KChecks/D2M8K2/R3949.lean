import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15796 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15796 = true := by
  decide +kernel

theorem tot15796 : totK PD2M8K2 D2M8K2.t15796 = [0, 168372991997, 467387754014, 263401077288, 21637161714, 0, 0, 0] := by
  decide +kernel

theorem rows15797 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15797 = true := by
  decide +kernel

theorem tot15797 : totK PD2M8K2 D2M8K2.t15797 = [0, 179476509406, 455228943503, 251296792217, 17989725014, 0, 0, 0] := by
  decide +kernel

theorem rows15798 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15798 = true := by
  decide +kernel

theorem tot15798 : totK PD2M8K2 D2M8K2.t15798 = [0, 0, 269570151692, 508279330578, 123405144059, 1268739303, 0, 0] := by
  decide +kernel

theorem rows15799 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15799 = true := by
  decide +kernel

theorem tot15799 : totK PD2M8K2 D2M8K2.t15799 = [0, 0, 178283137366, 480001983954, 211224526098, 8669917095, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
