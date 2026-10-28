import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4644 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4644 = true := by
  decide +kernel

theorem tot4644 : totK PA10K2 A10K2.t4644 = [0, 244073525254, 1350474742187, 2176961985457, 1125991024256, 121268983657, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4645 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4645 = true := by
  decide +kernel

theorem tot4645 : totK PA10K2 A10K2.t4645 = [0, 0, 609638351616, 2076259935989, 1926684075658, 405021978790, 13653259670, 0, 0, 0] := by
  decide +kernel

theorem rows4646 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4646 = true := by
  decide +kernel

theorem tot4646 : totK PA10K2 A10K2.t4646 = [0, 0, 391715337406, 1610495218896, 2121103707485, 827631712105, 61177778713, 0, 0, 0] := by
  decide +kernel

theorem rows4647 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4647 = true := by
  decide +kernel

theorem tot4647 : totK PA10K2 A10K2.t4647 = [0, 0, 199106461003, 1173863200814, 2116701765360, 1270446311412, 193065710970, 6318667960, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
