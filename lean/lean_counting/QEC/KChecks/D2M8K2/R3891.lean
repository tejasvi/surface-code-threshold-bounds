import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15564 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15564 = true := by
  decide +kernel

theorem tot15564 : totK PD2M8K2 D2M8K2.t15564 = [0, 0, 85033112404, 408609016573, 384171421934, 50240491348, 0, 0] := by
  decide +kernel

theorem rows15565 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15565 = true := by
  decide +kernel

theorem tot15565 : totK PD2M8K2 D2M8K2.t15565 = [0, 0, 71315772691, 345440006576, 390334025084, 83524175111, 1557581783, 0] := by
  decide +kernel

theorem rows15566 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15566 = true := by
  decide +kernel

theorem tot15566 : totK PD2M8K2 D2M8K2.t15566 = [0, 0, 171230700898, 441800084429, 272603749169, 30317129789, 0, 0] := by
  decide +kernel

theorem rows15567 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15567 = true := by
  decide +kernel

theorem tot15567 : totK PD2M8K2 D2M8K2.t15567 = [0, 0, 136346329562, 455292001889, 287950307883, 22732241413, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
