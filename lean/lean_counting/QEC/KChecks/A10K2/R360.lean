import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1440 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1440 = true := by
  decide +kernel

theorem tot1440 : totK PA10K2 A10K2.t1440 = [0, 0, 0, 292657876421, 1516515561528, 2109148700669, 704032714080, 45543540946, 0, 0] := by
  decide +kernel

theorem rows1441 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1441 = true := by
  decide +kernel

theorem tot1441 : totK PA10K2 A10K2.t1441 = [0, 0, 0, 292856431093, 1215613758520, 1890594682242, 1083285724919, 179533038711, 5546304973, 0] := by
  decide +kernel

theorem rows1442 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1442 = true := by
  decide +kernel

theorem tot1442 : totK PA10K2 A10K2.t1442 = [0, 0, 292156546580, 1145236244156, 1762895582641, 1435468085583, 418015451680, 29791859037, 0, 0] := by
  decide +kernel

theorem rows1443 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1443 = true := by
  decide +kernel

theorem tot1443 : totK PA10K2 A10K2.t1443 = [0, 0, 268742465433, 1479579831782, 2150871708811, 810965135090, 60081521450, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
