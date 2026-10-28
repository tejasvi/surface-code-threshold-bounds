import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10552 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10552 = true := by
  decide +kernel

theorem tot10552 : totK PD2M8K2 D2M8K2.t10552 = [0, 0, 84661032308, 339794936005, 378314416402, 110087965882, 8651220961, 0] := by
  decide +kernel

theorem rows10553 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10553 = true := by
  decide +kernel

theorem tot10553 : totK PD2M8K2 D2M8K2.t10553 = [0, 0, 0, 256183522583, 482187213292, 158026369186, 5173160209, 0] := by
  decide +kernel

theorem rows10554 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10554 = true := by
  decide +kernel

theorem tot10554 : totK PD2M8K2 D2M8K2.t10554 = [0, 0, 141085567007, 392716152274, 293529849898, 78286414890, 1353333895, 0] := by
  decide +kernel

theorem rows10555 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10555 = true := by
  decide +kernel

theorem tot10555 : totK PD2M8K2 D2M8K2.t10555 = [0, 0, 174617201078, 444913953927, 251224491077, 18072729198, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
