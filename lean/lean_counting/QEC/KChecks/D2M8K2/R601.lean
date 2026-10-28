import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2404 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2404 = true := by
  decide +kernel

theorem tot2404 : totK PD2M8K2 D2M8K2.t2404 = [0, 0, 171779119157, 440712761213, 251464864700, 21951979816, 0, 0] := by
  decide +kernel

theorem rows2405 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2405 = true := by
  decide +kernel

theorem tot2405 : totK PD2M8K2 D2M8K2.t2405 = [0, 36946381487, 188209286722, 432371802546, 230848710264, 9442392295, 0, 0] := by
  decide +kernel

theorem rows2406 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2406 = true := by
  decide +kernel

theorem tot2406 : totK PD2M8K2 D2M8K2.t2406 = [0, 174638904035, 449606550457, 251189348304, 22496526245, 0, 0, 0] := by
  decide +kernel

theorem rows2407 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2407 = true := by
  decide +kernel

theorem tot2407 : totK PD2M8K2 D2M8K2.t2407 = [0, 203545004969, 470076834560, 208306736540, 12317784814, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
