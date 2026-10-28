import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4440 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4440 = true := by
  decide +kernel

theorem tot4440 : totK PD2M8K2 D2M8K2.t4440 = [0, 149948691500, 365465801096, 276146940758, 106660884899, 6777409681, 0, 0] := by
  decide +kernel

theorem rows4441 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4441 = true := by
  decide +kernel

theorem tot4441 : totK PD2M8K2 D2M8K2.t4441 = [0, 170685305886, 444317730227, 281707189790, 30233312356, 0, 0, 0] := by
  decide +kernel

theorem rows4442 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4442 = true := by
  decide +kernel

theorem tot4442 : totK PD2M8K2 D2M8K2.t4442 = [0, 121787798155, 450130875659, 308704855173, 24802741333, 0, 0, 0] := by
  decide +kernel

theorem rows4443 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4443 = true := by
  decide +kernel

theorem tot4443 : totK PD2M8K2 D2M8K2.t4443 = [0, 0, 203367526602, 497859796716, 186322535792, 9587713104, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
