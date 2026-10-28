import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8132 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8132 = true := by
  decide +kernel

theorem tot8132 : totK PD2M8K2 D2M8K2.t8132 = [0, 192661276179, 462284654556, 251231358162, 23050312993, 0, 0, 0] := by
  decide +kernel

theorem rows8133 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8133 = true := by
  decide +kernel

theorem tot8133 : totK PD2M8K2 D2M8K2.t8133 = [0, 169061269896, 474661069933, 252991111632, 15098565248, 0, 0, 0] := by
  decide +kernel

theorem rows8134 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8134 = true := by
  decide +kernel

theorem tot8134 : totK PD2M8K2 D2M8K2.t8134 = [0, 0, 279728689550, 497395002737, 119219176281, 1268739303, 0, 0] := by
  decide +kernel

theorem rows8135 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8135 = true := by
  decide +kernel

theorem tot8135 : totK PD2M8K2 D2M8K2.t8135 = [0, 0, 204841784662, 485959060053, 187374330209, 7439461435, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
