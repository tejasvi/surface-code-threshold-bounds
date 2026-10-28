import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11124 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11124 = true := by
  decide +kernel

theorem tot11124 : totK PD2M8K2 D2M8K2.t11124 = [0, 88185535531, 311881330766, 384887587744, 98534693106, 3838026431, 0, 0] := by
  decide +kernel

theorem rows11125 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11125 = true := by
  decide +kernel

theorem tot11125 : totK PD2M8K2 D2M8K2.t11125 = [0, 142654551121, 447597161872, 271556864270, 16926626025, 0, 0, 0] := by
  decide +kernel

theorem rows11126 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11126 = true := by
  decide +kernel

theorem tot11126 : totK PD2M8K2 D2M8K2.t11126 = [0, 169213615022, 447499454396, 257819564115, 19412168197, 0, 0, 0] := by
  decide +kernel

theorem rows11127 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11127 = true := by
  decide +kernel

theorem tot11127 : totK PD2M8K2 D2M8K2.t11127 = [0, 0, 222034533899, 493080267638, 147289455715, 4928554699, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
