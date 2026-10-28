import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9968 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9968 = true := by
  decide +kernel

theorem tot9968 : totK PD2M8K2 D2M8K2.t9968 = [0, 0, 168704404144, 457480115890, 241940777904, 13665115269, 0, 0] := by
  decide +kernel

theorem rows9969 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9969 = true := by
  decide +kernel

theorem tot9969 : totK PD2M8K2 D2M8K2.t9969 = [0, 0, 0, 281059719031, 499992320567, 102911502027, 1369150432, 0] := by
  decide +kernel

theorem rows9970 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9970 = true := by
  decide +kernel

theorem tot9970 : totK PD2M8K2 D2M8K2.t9970 = [0, 0, 89898082331, 382132414398, 401689919636, 46125294614, 0, 0] := by
  decide +kernel

theorem rows9971 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9971 = true := by
  decide +kernel

theorem tot9971 : totK PD2M8K2 D2M8K2.t9971 = [0, 0, 185207838904, 461692495047, 239993081766, 17980865236, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
