import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1236 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1236 = true := by
  decide +kernel

theorem tot1236 : totK PA10K2 A10K2.t1236 = [0, 268742465433, 1499457451717, 2209761482103, 821276516437, 45879452064, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1237 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1237 = true := by
  decide +kernel

theorem tot1237 : totK PA10K2 A10K2.t1237 = [0, 409993224908, 1362383971473, 1688870403765, 1037644460439, 189668089786, 6034215561, 0, 0, 0] := by
  decide +kernel

theorem rows1238 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1238 = true := by
  decide +kernel

theorem tot1238 : totK PA10K2 A10K2.t1238 = [0, 329238616492, 1578625480444, 2073962694984, 701511920735, 53383554103, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1239 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1239 = true := by
  decide +kernel

theorem tot1239 : totK PA10K2 A10K2.t1239 = [0, 0, 699673135057, 2154960822534, 1535114167228, 263224096285, 6354482628, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
