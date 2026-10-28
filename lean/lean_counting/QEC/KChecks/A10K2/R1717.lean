import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6868 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6868 = true := by
  decide +kernel

theorem tot6868 : totK PA10K2 A10K2.t6868 = [0, 0, 395418495840, 1680252114185, 2084543556524, 792027658121, 62702525251, 0, 0, 0] := by
  decide +kernel

theorem rows6869 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6869 = true := by
  decide +kernel

theorem tot6869 : totK PA10K2 A10K2.t6869 = [0, 0, 261586904094, 1155209354901, 1935716519829, 1309265660045, 214449877947, 6439430839, 0, 0] := by
  decide +kernel

theorem rows6870 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6870 = true := by
  decide +kernel

theorem tot6870 : totK PA10K2 A10K2.t6870 = [0, 0, 459800043317, 1820146021327, 2060075959886, 555944581438, 22108643497, 0, 0, 0] := by
  decide +kernel

theorem rows6871 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6871 = true := by
  decide +kernel

theorem tot6871 : totK PA10K2 A10K2.t6871 = [0, 0, 165887444701, 1126383282754, 2117081382879, 1283624049401, 200282011859, 6021244195, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
