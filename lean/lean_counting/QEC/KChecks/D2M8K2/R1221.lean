import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4884 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4884 = true := by
  decide +kernel

theorem tot4884 : totK PD2M8K2 D2M8K2.t4884 = [0, 0, 0, 178718781984, 467865554753, 229138346940, 13725711977, 0] := by
  decide +kernel

theorem rows4885 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4885 = true := by
  decide +kernel

theorem tot4885 : totK PD2M8K2 D2M8K2.t4885 = [0, 0, 0, 0, 372070810193, 430129174119, 48591554820, 0] := by
  decide +kernel

theorem rows4886 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4886 = true := by
  decide +kernel

theorem tot4886 : totK PD2M8K2 D2M8K2.t4886 = [0, 0, 0, 167533123453, 403294577025, 245949134490, 52061410707, 1348424121] := by
  decide +kernel

theorem rows4887 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4887 = true := by
  decide +kernel

theorem tot4887 : totK PD2M8K2 D2M8K2.t4887 = [0, 0, 0, 244947172617, 472543816444, 176434388539, 8762656783, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
