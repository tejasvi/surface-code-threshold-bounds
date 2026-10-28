import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9704 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9704 = true := by
  decide +kernel

theorem tot9704 : totK PD2M8K2 D2M8K2.t9704 = [0, 80612415401, 325329387963, 367576166280, 100811254622, 3521263076, 0, 0] := by
  decide +kernel

theorem rows9705 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9705 = true := by
  decide +kernel

theorem tot9705 : totK PD2M8K2 D2M8K2.t9705 = [0, 188743378749, 465335551528, 256190144192, 18495306316, 0, 0, 0] := by
  decide +kernel

theorem rows9706 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9706 = true := by
  decide +kernel

theorem tot9706 : totK PD2M8K2 D2M8K2.t9706 = [0, 73060830560, 359477445862, 380509080570, 69528063531, 1096505104, 0, 0] := by
  decide +kernel

theorem rows9707 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9707 = true := by
  decide +kernel

theorem tot9707 : totK PD2M8K2 D2M8K2.t9707 = [0, 80691033710, 302870131282, 402928017499, 99920625525, 3821179711, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
