import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11576 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11576 = true := by
  decide +kernel

theorem tot11576 : totK PD2M8K2 D2M8K2.t11576 = [0, 259367977005, 501121460256, 129683079953, 1268739303, 0, 0, 0] := by
  decide +kernel

theorem rows11577 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11577 = true := by
  decide +kernel

theorem tot11577 : totK PD2M8K2 D2M8K2.t11577 = [0, 153530857576, 449908867208, 241784278032, 13702981038, 0, 0, 0] := by
  decide +kernel

theorem rows11578 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11578 = true := by
  decide +kernel

theorem tot11578 : totK PD2M8K2 D2M8K2.t11578 = [0, 197281319475, 466944055136, 212004682800, 16687972365, 0, 0, 0] := by
  decide +kernel

theorem rows11579 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11579 = true := by
  decide +kernel

theorem tot11579 : totK PD2M8K2 D2M8K2.t11579 = [0, 191490877538, 460006826642, 200325639902, 12206147664, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
