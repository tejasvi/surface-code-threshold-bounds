import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows624 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t624 = true := by
  decide +kernel

theorem tot624 : totK PD2M8K2 D2M8K2.t624 = [193844793842, 466931253487, 245844862221, 23245591409, 0, 0, 0, 0] := by
  decide +kernel

theorem rows625 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t625 = true := by
  decide +kernel

theorem tot625 : totK PD2M8K2 D2M8K2.t625 = [190645198667, 468956866397, 225508865298, 12491870267, 0, 0, 0, 0] := by
  decide +kernel

theorem rows626 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t626 = true := by
  decide +kernel

theorem tot626 : totK PD2M8K2 D2M8K2.t626 = [37979066117, 320391575001, 446260879126, 97337026433, 1197396724, 0, 0, 0] := by
  decide +kernel

theorem rows627 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t627 = true := by
  decide +kernel

theorem tot627 : totK PD2M8K2 D2M8K2.t627 = [0, 202055966831, 470254937085, 189239139112, 12040273252, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
