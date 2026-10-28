import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10436 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10436 = true := by
  decide +kernel

theorem tot10436 : totK PD2M8K2 D2M8K2.t10436 = [0, 0, 0, 202525227305, 485226336057, 191818104288, 10374152040, 0] := by
  decide +kernel

theorem rows10437 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10437 = true := by
  decide +kernel

theorem tot10437 : totK PD2M8K2 D2M8K2.t10437 = [0, 0, 0, 214229381402, 465975085586, 173802438981, 9656040098, 0] := by
  decide +kernel

theorem rows10438 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10438 = true := by
  decide +kernel

theorem tot10438 : totK PD2M8K2 D2M8K2.t10438 = [0, 0, 0, 84910640420, 386397226210, 320443564086, 50978048107, 1217496766] := by
  decide +kernel

theorem rows10439 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10439 = true := by
  decide +kernel

theorem tot10439 : totK PD2M8K2 D2M8K2.t10439 = [0, 0, 0, 19982995165, 336964129911, 442908018000, 58108799397, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
