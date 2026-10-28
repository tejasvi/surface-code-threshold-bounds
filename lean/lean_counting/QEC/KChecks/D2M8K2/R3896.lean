import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15584 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15584 = true := by
  decide +kernel

theorem tot15584 : totK PD2M8K2 D2M8K2.t15584 = [0, 0, 210266242536, 497669978992, 185201215503, 9587713104, 0, 0] := by
  decide +kernel

theorem rows15585 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15585 = true := by
  decide +kernel

theorem tot15585 : totK PD2M8K2 D2M8K2.t15585 = [0, 82968919721, 309335786477, 386205893610, 100602287777, 3462014130, 0, 0] := by
  decide +kernel

theorem rows15586 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15586 = true := by
  decide +kernel

theorem tot15586 : totK PD2M8K2 D2M8K2.t15586 = [0, 175823082858, 461864363865, 251178032921, 22569751235, 0, 0, 0] := by
  decide +kernel

theorem rows15587 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15587 = true := by
  decide +kernel

theorem tot15587 : totK PD2M8K2 D2M8K2.t15587 = [0, 141113630024, 450556215243, 271651835517, 17556675356, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
