import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15760 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15760 = true := by
  decide +kernel

theorem tot15760 : totK PD2M8K2 D2M8K2.t15760 = [0, 0, 92237621127, 360256269091, 361111033051, 61222250325, 1096505104, 0] := by
  decide +kernel

theorem rows15761 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15761 = true := by
  decide +kernel

theorem tot15761 : totK PD2M8K2 D2M8K2.t15761 = [0, 0, 0, 310950234497, 495538757996, 84955403166, 1069412848, 0] := by
  decide +kernel

theorem rows15762 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15762 = true := by
  decide +kernel

theorem tot15762 : totK PD2M8K2 D2M8K2.t15762 = [0, 0, 189589955382, 455436116517, 209225345727, 30733026910, 2814597007, 0] := by
  decide +kernel

theorem rows15763 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15763 = true := by
  decide +kernel

theorem tot15763 : totK PD2M8K2 D2M8K2.t15763 = [0, 0, 213277989812, 501821537310, 170824601206, 5186575791, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
