import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2696 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2696 = true := by
  decide +kernel

theorem tot2696 : totK PD2M8K2 D2M8K2.t2696 = [0, 51445543641, 335879330522, 421602589592, 80662992359, 1310517177, 0, 0] := by
  decide +kernel

theorem rows2697 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2697 = true := by
  decide +kernel

theorem tot2697 : totK PD2M8K2 D2M8K2.t2697 = [0, 93574619190, 387627681717, 391350839568, 48963631223, 0, 0, 0] := by
  decide +kernel

theorem rows2698 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2698 = true := by
  decide +kernel

theorem tot2698 : totK PD2M8K2 D2M8K2.t2698 = [0, 195314283470, 462495052238, 237985568903, 19429470416, 0, 0, 0] := by
  decide +kernel

theorem rows2699 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2699 = true := by
  decide +kernel

theorem tot2699 : totK PD2M8K2 D2M8K2.t2699 = [0, 142158439792, 444490747129, 286263156909, 31743473839, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
