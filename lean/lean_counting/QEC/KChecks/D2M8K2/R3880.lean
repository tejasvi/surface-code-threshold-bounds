import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15520 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15520 = true := by
  decide +kernel

theorem tot15520 : totK PD2M8K2 D2M8K2.t15520 = [0, 0, 278660975501, 501105563141, 118401576605, 1268739303, 0, 0] := by
  decide +kernel

theorem rows15521 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15521 = true := by
  decide +kernel

theorem tot15521 : totK PD2M8K2 D2M8K2.t15521 = [0, 0, 214363534877, 478833932468, 180309437829, 7442000727, 0, 0] := by
  decide +kernel

theorem rows15522 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15522 = true := by
  decide +kernel

theorem tot15522 : totK PD2M8K2 D2M8K2.t15522 = [0, 0, 183506273620, 479998727393, 220653359109, 14707859566, 0, 0] := by
  decide +kernel

theorem rows15523 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15523 = true := by
  decide +kernel

theorem tot15523 : totK PD2M8K2 D2M8K2.t15523 = [0, 0, 164900493963, 450955551742, 219590820645, 13534444894, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
