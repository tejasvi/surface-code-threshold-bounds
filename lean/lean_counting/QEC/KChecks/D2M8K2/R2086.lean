import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8344 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8344 = true := by
  decide +kernel

theorem tot8344 : totK PD2M8K2 D2M8K2.t8344 = [0, 206050880084, 497605593060, 190925239941, 5086124964, 0, 0, 0] := by
  decide +kernel

theorem rows8345 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8345 = true := by
  decide +kernel

theorem tot8345 : totK PD2M8K2 D2M8K2.t8345 = [0, 171414511721, 437338216220, 245732536097, 22828318141, 0, 0, 0] := by
  decide +kernel

theorem rows8346 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8346 = true := by
  decide +kernel

theorem tot8346 : totK PD2M8K2 D2M8K2.t8346 = [0, 92453491279, 385271775286, 333327532104, 53151371543, 1095107716, 0, 0] := by
  decide +kernel

theorem rows8347 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8347 = true := by
  decide +kernel

theorem tot8347 : totK PD2M8K2 D2M8K2.t8347 = [0, 0, 318529879422, 478734143499, 76037796880, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
