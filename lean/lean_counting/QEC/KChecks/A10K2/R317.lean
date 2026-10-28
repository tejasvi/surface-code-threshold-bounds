import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1268 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1268 = true := by
  decide +kernel

theorem tot1268 : totK PA10K2 A10K2.t1268 = [0, 0, 211669693007, 957968979455, 1905020352512, 1305516972937, 241719871907, 6354482628, 0, 0] := by
  decide +kernel

theorem rows1269 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1269 = true := by
  decide +kernel

theorem tot1269 : totK PA10K2 A10K2.t1269 = [0, 0, 436440854443, 1777815548312, 1977608845033, 553861253890, 32040661968, 0, 0, 0] := by
  decide +kernel

theorem rows1270 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1270 = true := by
  decide +kernel

theorem tot1270 : totK PA10K2 A10K2.t1270 = [0, 0, 102828163192, 966513142557, 2015597898011, 1336846185211, 298725765898, 24614390653, 0, 0] := by
  decide +kernel

theorem rows1271 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1271 = true := by
  decide +kernel

theorem tot1271 : totK PA10K2 A10K2.t1271 = [0, 0, 240806066827, 1107293419047, 1912961852005, 1202542006397, 182837972482, 5460492893, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
