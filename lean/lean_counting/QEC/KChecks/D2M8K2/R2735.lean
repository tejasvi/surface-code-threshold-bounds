import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10940 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10940 = true := by
  decide +kernel

theorem tot10940 : totK PD2M8K2 D2M8K2.t10940 = [0, 0, 0, 177392706071, 458525609674, 212487950039, 12430730167, 0] := by
  decide +kernel

theorem rows10941 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10941 = true := by
  decide +kernel

theorem tot10941 : totK PD2M8K2 D2M8K2.t10941 = [186677387228, 461439392893, 202050743940, 9852138406, 15566204914, 27006037035, 7077058802, 0] := by
  decide +kernel

theorem rows10942 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10942 = true := by
  decide +kernel

theorem tot10942 : totK PD2M8K2 D2M8K2.t10942 = [196248449448, 478165050033, 217276018899, 12534051746, 0, 0, 0, 0] := by
  decide +kernel

theorem rows10943 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10943 = true := by
  decide +kernel

theorem tot10943 : totK PD2M8K2 D2M8K2.t10943 = [55608356038, 328183325419, 424892254619, 92788249007, 1369150432, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
