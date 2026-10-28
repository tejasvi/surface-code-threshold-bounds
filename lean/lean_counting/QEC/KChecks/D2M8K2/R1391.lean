import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5564 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5564 = true := by
  decide +kernel

theorem tot5564 : totK PD2M8K2 D2M8K2.t5564 = [0, 178219018195, 472926520295, 250465051110, 17256164024, 0, 0, 0] := by
  decide +kernel

theorem rows5565 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5565 = true := by
  decide +kernel

theorem tot5565 : totK PD2M8K2 D2M8K2.t5565 = [0, 174201577589, 470214353807, 236522825167, 13291781812, 0, 0, 0] := by
  decide +kernel

theorem rows5566 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5566 = true := by
  decide +kernel

theorem tot5566 : totK PD2M8K2 D2M8K2.t5566 = [0, 0, 290502884892, 487497337374, 100531028091, 1162935789, 0, 0] := by
  decide +kernel

theorem rows5567 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5567 = true := by
  decide +kernel

theorem tot5567 : totK PD2M8K2 D2M8K2.t5567 = [0, 36272210802, 222036075972, 406411861202, 175695711152, 11853261585, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
