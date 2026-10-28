import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2352 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2352 = true := by
  decide +kernel

theorem tot2352 : totK PA10K2 A10K2.t2352 = [0, 409534657359, 1212325504948, 1466917361646, 1193274070422, 483657146272, 35768359878, 0, 0, 0] := by
  decide +kernel

theorem rows2353 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2353 = true := by
  decide +kernel

theorem tot2353 : totK PA10K2 A10K2.t2353 = [0, 173264853015, 1127981490455, 1911480866610, 1137967942938, 247067681469, 19641144955, 0, 0, 0] := by
  decide +kernel

theorem rows2354 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2354 = true := by
  decide +kernel

theorem tot2354 : totK PA10K2 A10K2.t2354 = [0, 299638544946, 1254732704493, 1834468598977, 1096706716737, 215923614192, 10760911071, 0, 0, 0] := by
  decide +kernel

theorem rows2355 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2355 = true := by
  decide +kernel

theorem tot2355 : totK PA10K2 A10K2.t2355 = [0, 469581908743, 1779665252443, 2011429591818, 587360139805, 32846095359, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
