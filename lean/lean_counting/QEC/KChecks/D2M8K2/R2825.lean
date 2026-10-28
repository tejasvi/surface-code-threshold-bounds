import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11300 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11300 = true := by
  decide +kernel

theorem tot11300 : totK PD2M8K2 D2M8K2.t11300 = [0, 234052288205, 494241260326, 168675161947, 8470662040, 0, 0, 0] := by
  decide +kernel

theorem rows11301 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11301 = true := by
  decide +kernel

theorem tot11301 : totK PD2M8K2 D2M8K2.t11301 = [97326488611, 336705075865, 352657135514, 94462435513, 3581949829, 0, 0, 0] := by
  decide +kernel

theorem rows11302 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11302 = true := by
  decide +kernel

theorem tot11302 : totK PD2M8K2 D2M8K2.t11302 = [176403517489, 435719549330, 267261307252, 30330618207, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11303 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11303 = true := by
  decide +kernel

theorem tot11303 : totK PD2M8K2 D2M8K2.t11303 = [140058034577, 451760622356, 285118546085, 23608171802, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
