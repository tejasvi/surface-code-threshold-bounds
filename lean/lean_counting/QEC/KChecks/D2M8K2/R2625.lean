import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10500 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10500 = true := by
  decide +kernel

theorem tot10500 : totK PD2M8K2 D2M8K2.t10500 = [0, 181990607809, 459283938082, 233346499865, 17115888737, 0, 0, 0] := by
  decide +kernel

theorem rows10501 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10501 = true := by
  decide +kernel

theorem tot10501 : totK PD2M8K2 D2M8K2.t10501 = [0, 140908836895, 439361514505, 284867116144, 23678717390, 0, 0, 0] := by
  decide +kernel

theorem rows10502 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10502 = true := by
  decide +kernel

theorem tot10502 : totK PD2M8K2 D2M8K2.t10502 = [0, 0, 273995449423, 509084447780, 110385113936, 1369150432, 0, 0] := by
  decide +kernel

theorem rows10503 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10503 = true := by
  decide +kernel

theorem tot10503 : totK PD2M8K2 D2M8K2.t10503 = [0, 140390059244, 428439866280, 301946050414, 32290312973, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
