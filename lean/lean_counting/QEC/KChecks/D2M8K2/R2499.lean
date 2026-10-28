import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9996 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9996 = true := by
  decide +kernel

theorem tot9996 : totK PD2M8K2 D2M8K2.t9996 = [0, 0, 174406166942, 444385207022, 270785116547, 22890933178, 0, 0] := by
  decide +kernel

theorem rows9997 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9997 = true := by
  decide +kernel

theorem tot9997 : totK PD2M8K2 D2M8K2.t9997 = [0, 0, 83129951559, 372583595787, 356999267905, 63910170059, 1198073392, 0] := by
  decide +kernel

theorem rows9998 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9998 = true := by
  decide +kernel

theorem tot9998 : totK PD2M8K2 D2M8K2.t9998 = [0, 0, 0, 256044286243, 488030902537, 139397562805, 8404294179, 0] := by
  decide +kernel

theorem rows9999 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9999 = true := by
  decide +kernel

theorem tot9999 : totK PD2M8K2 D2M8K2.t9999 = [0, 0, 141325792250, 369982326162, 297979354375, 73603699030, 3581949829, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
