import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11520 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11520 = true := by
  decide +kernel

theorem tot11520 : totK PD2M8K2 D2M8K2.t11520 = [0, 0, 214538126209, 470577296126, 193857884558, 8151738251, 0, 0] := by
  decide +kernel

theorem rows11521 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11521 = true := by
  decide +kernel

theorem tot11521 : totK PD2M8K2 D2M8K2.t11521 = [0, 0, 181696752146, 458847829827, 245633756390, 18246066036, 0, 0] := by
  decide +kernel

theorem rows11522 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11522 = true := by
  decide +kernel

theorem tot11522 : totK PD2M8K2 D2M8K2.t11522 = [0, 0, 164299400101, 483152481804, 217222643477, 6474224901, 0, 0] := by
  decide +kernel

theorem rows11523 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11523 = true := by
  decide +kernel

theorem tot11523 : totK PD2M8K2 D2M8K2.t11523 = [0, 0, 180163922697, 463427922335, 250604948679, 18333014298, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
