import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3548 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3548 = true := by
  decide +kernel

theorem tot3548 : totK PD2M8K2 D2M8K2.t3548 = [36923124222, 211275682143, 432587838822, 219140194904, 9326398835, 0, 0, 0] := by
  decide +kernel

theorem rows3549 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3549 = true := by
  decide +kernel

theorem tot3549 : totK PD2M8K2 D2M8K2.t3549 = [182031615137, 447717820683, 249042129121, 23125120004, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3550 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3550 = true := by
  decide +kernel

theorem tot3550 : totK PD2M8K2 D2M8K2.t3550 = [183888344036, 476697276925, 225718431153, 12373752831, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3551 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3551 = true := by
  decide +kernel

theorem tot3551 : totK PD2M8K2 D2M8K2.t3551 = [11896963338, 294484360240, 471015731199, 100747350570, 1164319620, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
