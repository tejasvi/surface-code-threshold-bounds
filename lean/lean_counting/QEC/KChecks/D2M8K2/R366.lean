import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1464 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1464 = true := by
  decide +kernel

theorem tot1464 : totK PD2M8K2 D2M8K2.t1464 = [0, 0, 210162143561, 476986398914, 208136849213, 10316589852, 0, 0] := by
  decide +kernel

theorem rows1465 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1465 = true := by
  decide +kernel

theorem tot1465 : totK PD2M8K2 D2M8K2.t1465 = [0, 176045873872, 371297813736, 216557915063, 122509989457, 13566916688, 0, 0] := by
  decide +kernel

theorem rows1466 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1466 = true := by
  decide +kernel

theorem tot1466 : totK PD2M8K2 D2M8K2.t1466 = [0, 152140554466, 455344395844, 248910899597, 14127568833, 0, 0, 0] := by
  decide +kernel

theorem rows1467 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1467 = true := by
  decide +kernel

theorem tot1467 : totK PD2M8K2 D2M8K2.t1467 = [0, 89561782785, 344650226873, 381045179131, 84064286334, 1369150432, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
