import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15388 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15388 = true := by
  decide +kernel

theorem tot15388 : totK PD2M8K2 D2M8K2.t15388 = [0, 0, 220276202070, 495480254777, 174938042047, 4967996017, 0, 0] := by
  decide +kernel

theorem rows15389 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15389 = true := by
  decide +kernel

theorem tot15389 : totK PD2M8K2 D2M8K2.t15389 = [0, 0, 193338646973, 460799128804, 219363682724, 17039442443, 0, 0] := by
  decide +kernel

theorem rows15390 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15390 = true := by
  decide +kernel

theorem tot15390 : totK PD2M8K2 D2M8K2.t15390 = [0, 0, 176483574964, 477607820993, 215320746364, 10922276178, 0, 0] := by
  decide +kernel

theorem rows15391 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15391 = true := by
  decide +kernel

theorem tot15391 : totK PD2M8K2 D2M8K2.t15391 = [0, 0, 84549453075, 359458125397, 359178342848, 65025892877, 1206465782, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
