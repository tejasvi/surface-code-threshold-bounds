import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15820 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15820 = true := by
  decide +kernel

theorem tot15820 : totK PD2M8K2 D2M8K2.t15820 = [0, 185527729733, 451628404059, 261192894659, 30615181147, 0, 0, 0] := by
  decide +kernel

theorem rows15821 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15821 = true := by
  decide +kernel

theorem tot15821 : totK PD2M8K2 D2M8K2.t15821 = [0, 187244704762, 468701070722, 227543565530, 12491870267, 0, 0, 0] := by
  decide +kernel

theorem rows15822 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15822 = true := by
  decide +kernel

theorem tot15822 : totK PD2M8K2 D2M8K2.t15822 = [0, 52337025351, 334450824350, 426602236037, 90586609534, 1197396724, 0, 0] := by
  decide +kernel

theorem rows15823 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15823 = true := by
  decide +kernel

theorem tot15823 : totK PD2M8K2 D2M8K2.t15823 = [0, 0, 191432479612, 466424205271, 193806270188, 12040273252, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
