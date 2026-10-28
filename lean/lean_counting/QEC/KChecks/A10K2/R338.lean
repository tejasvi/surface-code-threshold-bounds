import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1352 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1352 = true := by
  decide +kernel

theorem tot1352 : totK PA10K2 A10K2.t1352 = [0, 0, 0, 582057705654, 1994542677568, 1921408584052, 488871320445, 18540372887, 0, 0] := by
  decide +kernel

theorem rows1353 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1353 = true := by
  decide +kernel

theorem tot1353 : totK PA10K2 A10K2.t1353 = [0, 0, 0, 122511336145, 1042994249340, 2151188216452, 1348361629723, 206428673907, 6021244195, 0] := by
  decide +kernel

theorem rows1354 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1354 = true := by
  decide +kernel

theorem tot1354 : totK PA10K2 A10K2.t1354 = [0, 0, 213594577708, 426836266585, 786250285831, 1646952976482, 1521637525951, 445414575463, 29541060178, 0] := by
  decide +kernel

theorem rows1355 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1355 = true := by
  decide +kernel

theorem tot1355 : totK PA10K2 A10K2.t1355 = [0, 0, 436927437349, 1765265413077, 1990180350680, 558475875192, 32040661968, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
