import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8272 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8272 = true := by
  decide +kernel

theorem tot8272 : totK PD2M8K2 D2M8K2.t8272 = [0, 0, 292268984088, 482964199601, 98820738219, 1162935789, 0, 0] := by
  decide +kernel

theorem rows8273 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8273 = true := by
  decide +kernel

theorem tot8273 : totK PD2M8K2 D2M8K2.t8273 = [0, 7518713851, 199958615227, 443535125221, 181248616136, 11853261585, 0, 0] := by
  decide +kernel

theorem rows8274 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8274 = true := by
  decide +kernel

theorem tot8274 : totK PD2M8K2 D2M8K2.t8274 = [0, 206576871141, 474089302323, 204398825154, 11056080877, 0, 0, 0] := by
  decide +kernel

theorem rows8275 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8275 = true := by
  decide +kernel

theorem tot8275 : totK PD2M8K2 D2M8K2.t8275 = [0, 178281173022, 462358372423, 221997023274, 13144444366, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
