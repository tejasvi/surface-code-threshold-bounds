import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8044 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8044 = true := by
  decide +kernel

theorem tot8044 : totK PD2M8K2 D2M8K2.t8044 = [0, 0, 0, 175090235727, 474290630965, 227472894064, 12081080968, 0] := by
  decide +kernel

theorem rows8045 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8045 = true := by
  decide +kernel

theorem tot8045 : totK PD2M8K2 D2M8K2.t8045 = [0, 0, 0, 0, 327111087709, 439123178434, 74252725602, 1095107716] := by
  decide +kernel

theorem rows8046 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8046 = true := by
  decide +kernel

theorem tot8046 : totK PD2M8K2 D2M8K2.t8046 = [0, 160676680672, 334280267577, 100798778710, 54234435715, 166085210842, 70523764811, 3882006667] := by
  decide +kernel

theorem rows8047 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8047 = true := by
  decide +kernel

theorem tot8047 : totK PD2M8K2 D2M8K2.t8047 = [0, 184131877305, 445275928490, 232192483948, 17115888737, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
