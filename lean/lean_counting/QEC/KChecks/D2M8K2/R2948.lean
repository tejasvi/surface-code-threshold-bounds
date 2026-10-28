import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11792 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11792 = true := by
  decide +kernel

theorem tot11792 : totK PD2M8K2 D2M8K2.t11792 = [0, 171259142256, 443240368228, 261316383699, 27916441935, 0, 0, 0] := by
  decide +kernel

theorem rows11793 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11793 = true := by
  decide +kernel

theorem tot11793 : totK PD2M8K2 D2M8K2.t11793 = [0, 211286576812, 468838761213, 206379618752, 14187292541, 0, 0, 0] := by
  decide +kernel

theorem rows11794 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11794 = true := by
  decide +kernel

theorem tot11794 : totK PD2M8K2 D2M8K2.t11794 = [0, 36108306995, 338315354442, 431135925266, 73680089871, 1062926506, 0, 0] := by
  decide +kernel

theorem rows11795 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11795 = true := by
  decide +kernel

theorem tot11795 : totK PD2M8K2 D2M8K2.t11795 = [0, 40231679803, 286059576816, 457070530501, 108711591986, 3783381897, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
