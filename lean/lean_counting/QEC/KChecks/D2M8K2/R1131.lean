import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4524 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4524 = true := by
  decide +kernel

theorem tot4524 : totK PD2M8K2 D2M8K2.t4524 = [0, 0, 73899082759, 367089697862, 420302345167, 42822884289, 0, 0] := by
  decide +kernel

theorem rows4525 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4525 = true := by
  decide +kernel

theorem tot4525 : totK PD2M8K2 D2M8K2.t4525 = [0, 0, 168417944713, 445053727894, 278714888295, 28529815567, 0, 0] := by
  decide +kernel

theorem rows4526 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4526 = true := by
  decide +kernel

theorem tot4526 : totK PD2M8K2 D2M8K2.t4526 = [0, 0, 177612720904, 485886047819, 250971688578, 10512015155, 0, 0] := by
  decide +kernel

theorem rows4527 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4527 = true := by
  decide +kernel

theorem tot4527 : totK PD2M8K2 D2M8K2.t4527 = [0, 0, 170687054936, 447961865952, 253677382636, 24637591875, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
