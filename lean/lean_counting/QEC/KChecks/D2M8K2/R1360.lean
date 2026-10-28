import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5440 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5440 = true := by
  decide +kernel

theorem tot5440 : totK PD2M8K2 D2M8K2.t5440 = [0, 0, 0, 194469114857, 482727025536, 209672539922, 9695001335, 0] := by
  decide +kernel

theorem rows5441 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5441 = true := by
  decide +kernel

theorem tot5441 : totK PD2M8K2 D2M8K2.t5441 = [0, 0, 156214179190, 335587858044, 257796836186, 129168540303, 12074255777, 0] := by
  decide +kernel

theorem rows5442 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5442 = true := by
  decide +kernel

theorem tot5442 : totK PD2M8K2 D2M8K2.t5442 = [0, 0, 219541710748, 486326845082, 199163594583, 9854352749, 0, 0] := by
  decide +kernel

theorem rows5443 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5443 = true := by
  decide +kernel

theorem tot5443 : totK PD2M8K2 D2M8K2.t5443 = [0, 0, 0, 294841249673, 487907867936, 91649735850, 1369150432, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
