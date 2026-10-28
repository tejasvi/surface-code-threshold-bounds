import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10004 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10004 = true := by
  decide +kernel

theorem tot10004 : totK PD2M8K2 D2M8K2.t10004 = [0, 0, 172490769739, 458734899871, 229978686501, 13790237889, 0, 0] := by
  decide +kernel

theorem rows10005 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10005 = true := by
  decide +kernel

theorem tot10005 : totK PD2M8K2 D2M8K2.t10005 = [0, 0, 89411507079, 368714260942, 363054449840, 66970250152, 1369150432, 0] := by
  decide +kernel

theorem rows10006 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10006 = true := by
  decide +kernel

theorem tot10006 : totK PD2M8K2 D2M8K2.t10006 = [0, 0, 0, 314717318360, 510059359487, 67573722478, 0, 0] := by
  decide +kernel

theorem rows10007 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10007 = true := by
  decide +kernel

theorem tot10007 : totK PD2M8K2 D2M8K2.t10007 = [0, 0, 183557299978, 441209741938, 274455713396, 31803820147, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
