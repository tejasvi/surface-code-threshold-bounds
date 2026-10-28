import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11252 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11252 = true := by
  decide +kernel

theorem tot11252 : totK PD2M8K2 D2M8K2.t11252 = [0, 177177287391, 465574376780, 248672252988, 12907470995, 0, 0, 0] := by
  decide +kernel

theorem rows11253 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11253 = true := by
  decide +kernel

theorem tot11253 : totK PD2M8K2 D2M8K2.t11253 = [0, 0, 285590595460, 487487050916, 116237773031, 1238673482, 0, 0] := by
  decide +kernel

theorem rows11254 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11254 = true := by
  decide +kernel

theorem tot11254 : totK PD2M8K2 D2M8K2.t11254 = [85410234403, 150179614450, 143034356710, 329332713169, 159704578765, 8063697217, 0, 0] := by
  decide +kernel

theorem rows11255 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11255 = true := by
  decide +kernel

theorem tot11255 : totK PD2M8K2 D2M8K2.t11255 = [170751651791, 482499072979, 231925580128, 9563601265, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
