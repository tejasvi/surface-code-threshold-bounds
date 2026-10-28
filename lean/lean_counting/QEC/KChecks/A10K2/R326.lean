import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1304 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1304 = true := by
  decide +kernel

theorem tot1304 : totK PA10K2 A10K2.t1304 = [0, 300827602965, 1122416130602, 1623475745330, 1363507306921, 544507131509, 50555834002, 0, 0, 0] := by
  decide +kernel

theorem rows1305 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1305 = true := by
  decide +kernel

theorem tot1305 : totK PA10K2 A10K2.t1305 = [0, 481111462414, 1799305562005, 1988130642301, 625624168834, 38659061916, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1306 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1306 = true := by
  decide +kernel

theorem tot1306 : totK PA10K2 A10K2.t1306 = [0, 0, 608752156527, 2043127659127, 1739739681057, 408316092316, 25295400199, 0, 0, 0] := by
  decide +kernel

theorem rows1307 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1307 = true := by
  decide +kernel

theorem tot1307 : totK PA10K2 A10K2.t1307 = [0, 323829410999, 1383561386308, 2014877734387, 1102971428271, 173974317797, 5453753178, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
