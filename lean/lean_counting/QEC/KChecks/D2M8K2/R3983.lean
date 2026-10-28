import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15932 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15932 = true := by
  decide +kernel

theorem tot15932 : totK PD2M8K2 D2M8K2.t15932 = [0, 182433760473, 475836808179, 254465538992, 14972817685, 0, 0, 0] := by
  decide +kernel

theorem rows15933 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15933 = true := by
  decide +kernel

theorem tot15933 : totK PD2M8K2 D2M8K2.t15933 = [0, 0, 258950969760, 511619671297, 130489486807, 1268739303, 0, 0] := by
  decide +kernel

theorem rows15934 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15934 = true := by
  decide +kernel

theorem tot15934 : totK PD2M8K2 D2M8K2.t15934 = [0, 0, 181091003179, 484688829875, 213815819969, 8669917095, 0, 0] := by
  decide +kernel

theorem rows15935 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15935 = true := by
  decide +kernel

theorem tot15935 : totK PD2M8K2 D2M8K2.t15935 = [0, 0, 168313338008, 463473122632, 232611607194, 17446192760, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
