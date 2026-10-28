import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8236 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8236 = true := by
  decide +kernel

theorem tot8236 : totK PD2M8K2 D2M8K2.t8236 = [0, 221738784898, 484380767911, 160261386793, 3699256714, 0, 0, 0] := by
  decide +kernel

theorem rows8237 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8237 = true := by
  decide +kernel

theorem tot8237 : totK PD2M8K2 D2M8K2.t8237 = [0, 195298533513, 461619605310, 216877109224, 17080783126, 0, 0, 0] := by
  decide +kernel

theorem rows8238 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8238 = true := by
  decide +kernel

theorem tot8238 : totK PD2M8K2 D2M8K2.t8238 = [0, 173773632270, 480534149661, 217830722492, 10797020908, 0, 0, 0] := by
  decide +kernel

theorem rows8239 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8239 = true := by
  decide +kernel

theorem tot8239 : totK PD2M8K2 D2M8K2.t8239 = [0, 174681990209, 473941679729, 219983195336, 12281934379, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
