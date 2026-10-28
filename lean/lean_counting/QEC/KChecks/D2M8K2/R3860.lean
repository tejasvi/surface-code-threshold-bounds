import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15440 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15440 = true := by
  decide +kernel

theorem tot15440 : totK PD2M8K2 D2M8K2.t15440 = [0, 175136962813, 473199800641, 247813394539, 14659527153, 0, 0, 0] := by
  decide +kernel

theorem rows15441 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15441 = true := by
  decide +kernel

theorem tot15441 : totK PD2M8K2 D2M8K2.t15441 = [0, 73710269914, 328719671197, 369140707946, 130319771924, 15863492353, 0, 0] := by
  decide +kernel

theorem rows15442 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15442 = true := by
  decide +kernel

theorem tot15442 : totK PD2M8K2 D2M8K2.t15442 = [0, 0, 175997321195, 462099128100, 239448365708, 13527618342, 0, 0] := by
  decide +kernel

theorem rows15443 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15443 = true := by
  decide +kernel

theorem tot15443 : totK PD2M8K2 D2M8K2.t15443 = [0, 53143458605, 233728818374, 415941203253, 193078261892, 8210597527, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
