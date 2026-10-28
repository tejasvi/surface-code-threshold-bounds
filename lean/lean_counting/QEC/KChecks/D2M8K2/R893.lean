import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3572 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3572 = true := by
  decide +kernel

theorem tot3572 : totK PD2M8K2 D2M8K2.t3572 = [0, 175848297049, 452731077976, 254323203528, 22828318141, 0, 0, 0] := by
  decide +kernel

theorem rows3573 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3573 = true := by
  decide +kernel

theorem tot3573 : totK PD2M8K2 D2M8K2.t3573 = [0, 125257021231, 439986922872, 294183912625, 24237313032, 0, 0, 0] := by
  decide +kernel

theorem rows3574 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3574 = true := by
  decide +kernel

theorem tot3574 : totK PD2M8K2 D2M8K2.t3574 = [0, 0, 303456364435, 469611203782, 90566707796, 1095107716, 0, 0] := by
  decide +kernel

theorem rows3575 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3575 = true := by
  decide +kernel

theorem tot3575 : totK PD2M8K2 D2M8K2.t3575 = [0, 155865311620, 373358227797, 273374480224, 85555993417, 3882006667, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
