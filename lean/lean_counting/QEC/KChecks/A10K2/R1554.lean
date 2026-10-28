import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6216 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6216 = true := by
  decide +kernel

theorem tot6216 : totK PA10K2 A10K2.t6216 = [0, 0, 77332580764, 900172527765, 2200474343998, 1550600382710, 267855156468, 6853348008, 0, 0] := by
  decide +kernel

theorem rows6217 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6217 = true := by
  decide +kernel

theorem tot6217 : totK PA10K2 A10K2.t6217 = [0, 0, 499952349042, 1895913884367, 1878240908237, 447928114299, 25686058060, 0, 0, 0] := by
  decide +kernel

theorem rows6218 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6218 = true := by
  decide +kernel

theorem tot6218 : totK PA10K2 A10K2.t6218 = [0, 0, 184672429309, 1036980809330, 1967284401840, 1260762730959, 250838269310, 19313972475, 0, 0] := by
  decide +kernel

theorem rows6219 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6219 = true := by
  decide +kernel

theorem tot6219 : totK PA10K2 A10K2.t6219 = [0, 0, 279438172082, 1124665488387, 1895404309338, 1206672738356, 216478140562, 10760911071, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
