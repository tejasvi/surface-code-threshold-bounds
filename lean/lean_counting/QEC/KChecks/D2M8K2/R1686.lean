import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6744 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6744 = true := by
  decide +kernel

theorem tot6744 : totK PD2M8K2 D2M8K2.t6744 = [0, 243453086884, 486256252751, 153136287219, 3699256714, 0, 0, 0] := by
  decide +kernel

theorem rows6745 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6745 = true := by
  decide +kernel

theorem tot6745 : totK PD2M8K2 D2M8K2.t6745 = [0, 184110442286, 466950225075, 219835516636, 17080783126, 0, 0, 0] := by
  decide +kernel

theorem rows6746 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6746 = true := by
  decide +kernel

theorem tot6746 : totK PD2M8K2 D2M8K2.t6746 = [0, 171299158750, 471561375676, 221201605845, 10797020908, 0, 0, 0] := by
  decide +kernel

theorem rows6747 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6747 = true := by
  decide +kernel

theorem tot6747 : totK PD2M8K2 D2M8K2.t6747 = [0, 168847795753, 458548488649, 227495358103, 14845936859, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
