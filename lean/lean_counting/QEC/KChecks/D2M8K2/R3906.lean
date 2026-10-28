import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15624 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15624 = true := by
  decide +kernel

theorem tot15624 : totK PD2M8K2 D2M8K2.t15624 = [0, 0, 289973718308, 520226132047, 97801853457, 1096505104, 0, 0] := by
  decide +kernel

theorem rows15625 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15625 = true := by
  decide +kernel

theorem tot15625 : totK PD2M8K2 D2M8K2.t15625 = [0, 0, 210208606097, 493561652755, 179136388724, 5253830308, 0, 0] := by
  decide +kernel

theorem rows15626 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15626 = true := by
  decide +kernel

theorem tot15626 : totK PD2M8K2 D2M8K2.t15626 = [0, 0, 186554366991, 473661476269, 193600790700, 10637711188, 0, 0] := by
  decide +kernel

theorem rows15627 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15627 = true := by
  decide +kernel

theorem tot15627 : totK PD2M8K2 D2M8K2.t15627 = [0, 0, 66978833158, 369107492570, 355873013624, 52355325953, 1138244013, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
