import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15012 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15012 = true := by
  decide +kernel

theorem tot15012 : totK PD2M8K2 D2M8K2.t15012 = [0, 161643786430, 442375369658, 282623445027, 27984307814, 0, 0, 0] := by
  decide +kernel

theorem rows15013 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15013 = true := by
  decide +kernel

theorem tot15013 : totK PD2M8K2 D2M8K2.t15013 = [0, 92934196222, 360096192058, 372083632759, 70845630846, 1268739303, 0, 0] := by
  decide +kernel

theorem rows15014 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15014 = true := by
  decide +kernel

theorem tot15014 : totK PD2M8K2 D2M8K2.t15014 = [0, 0, 248980884929, 497106452533, 149581486436, 3630467006, 0, 0] := by
  decide +kernel

theorem rows15015 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15015 = true := by
  decide +kernel

theorem tot15015 : totK PD2M8K2 D2M8K2.t15015 = [0, 0, 181554460702, 462438035271, 221559585021, 17076867616, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
