import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10112 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10112 = true := by
  decide +kernel

theorem tot10112 : totK PD2M8K2 D2M8K2.t10112 = [0, 0, 161633475954, 451611711398, 282736407729, 23526837644, 0, 0] := by
  decide +kernel

theorem rows10113 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10113 = true := by
  decide +kernel

theorem tot10113 : totK PD2M8K2 D2M8K2.t10113 = [0, 0, 174018067377, 476410231078, 237822801945, 11708418744, 0, 0] := by
  decide +kernel

theorem rows10114 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10114 = true := by
  decide +kernel

theorem tot10114 : totK PD2M8K2 D2M8K2.t10114 = [0, 0, 178486149385, 447789488801, 255134921295, 26507925613, 0, 0] := by
  decide +kernel

theorem rows10115 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10115 = true := by
  decide +kernel

theorem tot10115 : totK PD2M8K2 D2M8K2.t10115 = [0, 0, 190847917919, 482360619577, 218422110551, 12439805748, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
