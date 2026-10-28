import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1424 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1424 = true := by
  decide +kernel

theorem tot1424 : totK PA10K2 A10K2.t1424 = [0, 0, 0, 269682608971, 1112256775690, 1929986294118, 1412362508595, 270610126127, 14941726116, 0] := by
  decide +kernel

theorem rows1425 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1425 = true := by
  decide +kernel

theorem tot1425 : totK PA10K2 A10K2.t1425 = [0, 0, 0, 530897183272, 1968556850798, 2013982934184, 557728641981, 37205212510, 0, 0] := by
  decide +kernel

theorem rows1426 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1426 = true := by
  decide +kernel

theorem tot1426 : totK PA10K2 A10K2.t1426 = [0, 0, 0, 499381935060, 1922388400209, 1994943533720, 580935509118, 36947751476, 0, 0] := by
  decide +kernel

theorem rows1427 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1427 = true := by
  decide +kernel

theorem tot1427 : totK PA10K2 A10K2.t1427 = [0, 0, 0, 0, 763737589941, 2280531552044, 1704370547604, 272357642451, 6853348008, 0] := by
  decide +kernel

end QECKChecks.A10K2
