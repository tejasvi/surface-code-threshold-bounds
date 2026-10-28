import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7984 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7984 = true := by
  decide +kernel

theorem tot7984 : totK PA10K2 A10K2.t7984 = [0, 0, 0, 529693990345, 1868676229527, 1961107550161, 540893775100, 22108643497, 0, 0] := by
  decide +kernel

theorem rows7985 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7985 = true := by
  decide +kernel

theorem tot7985 : totK PA10K2 A10K2.t7985 = [0, 0, 0, 225901357694, 1336792598756, 2183366778727, 1086042370991, 111911495362, 0, 0] := by
  decide +kernel

theorem rows7986 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7986 = true := by
  decide +kernel

theorem tot7986 : totK PA10K2 A10K2.t7986 = [0, 0, 0, 0, 599145896583, 2039728555446, 1854357420449, 387491171951, 12132367858, 0] := by
  decide +kernel

theorem rows7987 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7987 = true := by
  decide +kernel

theorem tot7987 : totK PA10K2 A10K2.t7987 = [0, 0, 396273731552, 1250093511923, 1271394094012, 661863211616, 821897471888, 461786661359, 48886019071, 0] := by
  decide +kernel

end QECKChecks.A10K2
