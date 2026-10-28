import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7968 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7968 = true := by
  decide +kernel

theorem tot7968 : totK PA10K2 A10K2.t7968 = [0, 0, 0, 710949414406, 2210544406207, 1766494355376, 299137443352, 6315661314, 0, 0] := by
  decide +kernel

theorem rows7969 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7969 = true := by
  decide +kernel

theorem tot7969 : totK PA10K2 A10K2.t7969 = [0, 0, 0, 320136002803, 1574945715347, 2249683283243, 854952198753, 48663178155, 0, 0] := by
  decide +kernel

theorem rows7970 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7970 = true := by
  decide +kernel

theorem tot7970 : totK PA10K2 A10K2.t7970 = [0, 0, 576058160402, 1951291226415, 1832737764848, 419776892322, 23654769259, 0, 0, 0] := by
  decide +kernel

theorem rows7971 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7971 = true := by
  decide +kernel

theorem tot7971 : totK PA10K2 A10K2.t7971 = [0, 0, 178075110047, 1134720676487, 2100441505736, 1295959667837, 251278687889, 11991740650, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
