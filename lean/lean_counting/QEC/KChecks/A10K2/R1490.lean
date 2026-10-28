import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5960 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5960 = true := by
  decide +kernel

theorem tot5960 : totK PA10K2 A10K2.t5960 = [0, 0, 574022706119, 1951501328673, 1730321889856, 411824258715, 25371180993, 0, 0, 0] := by
  decide +kernel

theorem rows5961 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5961 = true := by
  decide +kernel

theorem tot5961 : totK PA10K2 A10K2.t5961 = [0, 251705348851, 1286101980281, 1962052904335, 1062345484591, 172150510515, 5460492893, 0, 0, 0] := by
  decide +kernel

theorem rows5962 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5962 = true := by
  decide +kernel

theorem tot5962 : totK PA10K2 A10K2.t5962 = [0, 413094667242, 1388614499100, 1772488272225, 967982602306, 167593583403, 6034215561, 0, 0, 0] := by
  decide +kernel

theorem rows5963 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5963 = true := by
  decide +kernel

theorem tot5963 : totK PA10K2 A10K2.t5963 = [0, 328626408132, 1578266444313, 1966512454070, 670892992868, 52620687920, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
