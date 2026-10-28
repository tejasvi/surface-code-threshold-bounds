import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12012 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12012 = true := by
  decide +kernel

theorem tot12012 : totK PD2M8K2 D2M8K2.t12012 = [145886318465, 360552356328, 277586576232, 107195163065, 6804944647, 0, 0, 0] := by
  decide +kernel

theorem rows12013 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12013 = true := by
  decide +kernel

theorem tot12013 : totK PD2M8K2 D2M8K2.t12013 = [168374393994, 437905011713, 279976402998, 30182954071, 0, 0, 0, 0] := by
  decide +kernel

theorem rows12014 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12014 = true := by
  decide +kernel

theorem tot12014 : totK PD2M8K2 D2M8K2.t12014 = [107587333398, 430343890103, 337232581246, 28987237680, 0, 0, 0, 0] := by
  decide +kernel

theorem rows12015 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12015 = true := by
  decide +kernel

theorem tot12015 : totK PD2M8K2 D2M8K2.t12015 = [0, 206486499409, 482818049796, 188005512993, 9664716404, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
