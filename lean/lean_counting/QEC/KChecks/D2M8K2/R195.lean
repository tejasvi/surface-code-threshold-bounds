import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows780 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t780 = true := by
  decide +kernel

theorem tot780 : totK PD2M8K2 D2M8K2.t780 = [0, 0, 19320235271, 336590802938, 420510004550, 74763977611, 1310517177, 0] := by
  decide +kernel

theorem rows781 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t781 = true := by
  decide +kernel

theorem tot781 : totK PD2M8K2 D2M8K2.t781 = [0, 0, 89804421751, 414857832404, 314493641720, 31352939056, 0, 0] := by
  decide +kernel

theorem rows782 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t782 = true := by
  decide +kernel

theorem tot782 : totK PD2M8K2 D2M8K2.t782 = [0, 0, 225559161483, 497068151320, 147687214610, 2227891822, 0, 0] := by
  decide +kernel

theorem rows783 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t783 = true := by
  decide +kernel

theorem tot783 : totK PD2M8K2 D2M8K2.t783 = [0, 0, 217408080491, 490158257175, 181697285326, 5488283679, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
