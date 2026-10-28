import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7000 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7000 = true := by
  decide +kernel

theorem tot7000 : totK PA10K2 A10K2.t7000 = [0, 0, 462024271497, 1861938565701, 2042091250448, 582835194022, 29194255750, 0, 0, 0] := by
  decide +kernel

theorem rows7001 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7001 = true := by
  decide +kernel

theorem tot7001 : totK PA10K2 A10K2.t7001 = [0, 0, 327251851251, 1453363884818, 2153750036193, 982879234667, 75690751338, 0, 0, 0] := by
  decide +kernel

theorem rows7002 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7002 = true := by
  decide +kernel

theorem tot7002 : totK PA10K2 A10K2.t7002 = [0, 0, 0, 609712862174, 2032824739443, 1913341603425, 418924467727, 13244237517, 0, 0] := by
  decide +kernel

theorem rows7003 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7003 = true := by
  decide +kernel

theorem tot7003 : totK PA10K2 A10K2.t7003 = [0, 310694887869, 1064754319822, 1107142119381, 759346737757, 1045526397236, 506914864948, 49137922124, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
