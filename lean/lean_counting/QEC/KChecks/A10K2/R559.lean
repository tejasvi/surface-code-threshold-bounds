import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2236 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2236 = true := by
  decide +kernel

theorem tot2236 : totK PA10K2 A10K2.t2236 = [0, 579960394739, 1788586110348, 1669647177740, 669774551743, 251603711761, 37674658091, 0, 0, 0] := by
  decide +kernel

theorem rows2237 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2237 = true := by
  decide +kernel

theorem tot2237 : totK PA10K2 A10K2.t2237 = [0, 45274709553, 818961758335, 2165018671567, 1597165907022, 332415062963, 11991740650, 0, 0, 0] := by
  decide +kernel

theorem rows2238 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2238 = true := by
  decide +kernel

theorem tot2238 : totK PA10K2 A10K2.t2238 = [0, 374058291720, 1501354510376, 2060107506654, 930001701613, 92190613534, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2239 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2239 = true := by
  decide +kernel

theorem tot2239 : totK PA10K2 A10K2.t2239 = [0, 411116657375, 1792503071045, 2126874744941, 707645290697, 51303630972, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
