import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6380 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6380 = true := by
  decide +kernel

theorem tot6380 : totK PD2M8K2 D2M8K2.t6380 = [0, 0, 87382242367, 342542290385, 366545727820, 77371494135, 1162935789, 0] := by
  decide +kernel

theorem rows6381 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6381 = true := by
  decide +kernel

theorem tot6381 : totK PD2M8K2 D2M8K2.t6381 = [0, 0, 0, 240547869941, 458242314407, 154713151139, 9389920916, 0] := by
  decide +kernel

theorem rows6382 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6382 = true := by
  decide +kernel

theorem tot6382 : totK PD2M8K2 D2M8K2.t6382 = [0, 0, 162081603104, 406866445309, 244960892860, 49214646688, 2463340669, 0] := by
  decide +kernel

theorem rows6383 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6383 = true := by
  decide +kernel

theorem tot6383 : totK PD2M8K2 D2M8K2.t6383 = [0, 0, 159219192853, 454644222207, 241503921523, 19113238547, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
