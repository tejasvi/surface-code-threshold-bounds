import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows364 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t364 = true := by
  decide +kernel

theorem tot364 : totK PD2M8K2 D2M8K2.t364 = [107546192194, 347289184158, 337841669826, 94303439125, 3884009855, 0, 0, 0] := by
  decide +kernel

theorem rows365 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t365 = true := by
  decide +kernel

theorem tot365 : totK PD2M8K2 D2M8K2.t365 = [165953698885, 442399196424, 268800911116, 29541966104, 0, 0, 0, 0] := by
  decide +kernel

theorem rows366 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t366 = true := by
  decide +kernel

theorem tot366 : totK PD2M8K2 D2M8K2.t366 = [143213822991, 438410734848, 303838248441, 23594185146, 0, 0, 0, 0] := by
  decide +kernel

theorem rows367 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t367 = true := by
  decide +kernel

theorem tot367 : totK PD2M8K2 D2M8K2.t367 = [0, 207276099289, 495170885027, 174272255522, 4967996017, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
