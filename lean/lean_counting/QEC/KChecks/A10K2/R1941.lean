import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7764 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7764 = true := by
  decide +kernel

theorem tot7764 : totK PA10K2 A10K2.t7764 = [0, 0, 494894354109, 1868438613002, 1762043699227, 421656957175, 25371180993, 0, 0, 0] := by
  decide +kernel

theorem rows7765 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7765 = true := by
  decide +kernel

theorem tot7765 : totK PA10K2 A10K2.t7765 = [0, 348823104215, 1403611063503, 1972024959596, 994986451091, 159211838550, 5460492893, 0, 0, 0] := by
  decide +kernel

theorem rows7766 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7766 = true := by
  decide +kernel

theorem tot7766 : totK PA10K2 A10K2.t7766 = [0, 233657900939, 1442879720002, 2143571070208, 786596650815, 52292001731, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7767 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7767 = true := by
  decide +kernel

theorem tot7767 : totK PA10K2 A10K2.t7767 = [0, 336716992438, 1272481677534, 1849117964906, 1080683496777, 182907304986, 6354482628, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
