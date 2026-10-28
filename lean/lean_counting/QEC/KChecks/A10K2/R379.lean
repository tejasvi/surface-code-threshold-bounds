import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1516 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1516 = true := by
  decide +kernel

theorem tot1516 : totK PA10K2 A10K2.t1516 = [0, 0, 0, 325864898897, 1535129573306, 2173281822459, 872829927293, 62762815243, 0, 0] := by
  decide +kernel

theorem rows1517 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1517 = true := by
  decide +kernel

theorem tot1517 : totK PA10K2 A10K2.t1517 = [0, 0, 0, 0, 571876073948, 1946970744451, 2000267150375, 538938351810, 35608018656, 0] := by
  decide +kernel

theorem rows1518 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1518 = true := by
  decide +kernel

theorem tot1518 : totK PA10K2 A10K2.t1518 = [0, 567045256406, 1968769078711, 1850534908123, 444168737465, 25686058060, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1519 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1519 = true := by
  decide +kernel

theorem tot1519 : totK PA10K2 A10K2.t1519 = [0, 274878282901, 1415526287127, 2178110748821, 944743375456, 75709679393, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
