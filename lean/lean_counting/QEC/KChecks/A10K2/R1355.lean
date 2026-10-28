import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5420 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5420 = true := by
  decide +kernel

theorem tot5420 : totK PA10K2 A10K2.t5420 = [0, 0, 0, 599617814298, 2174925098544, 1909168482953, 341799043452, 6962742351, 0, 0] := by
  decide +kernel

theorem rows5421 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5421 = true := by
  decide +kernel

theorem tot5421 : totK PA10K2 A10K2.t5421 = [0, 0, 0, 460236777099, 1671073947898, 1938732907168, 689614343044, 55943954200, 0, 0] := by
  decide +kernel

theorem rows5422 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5422 = true := by
  decide +kernel

theorem tot5422 : totK PA10K2 A10K2.t5422 = [0, 0, 0, 398047221139, 1787719135158, 2039297679462, 561018541560, 35016950841, 0, 0] := by
  decide +kernel

theorem rows5423 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5423 = true := by
  decide +kernel

theorem tot5423 : totK PA10K2 A10K2.t5423 = [0, 0, 0, 0, 450764723641, 1836017071988, 1803971079459, 433970489345, 25565504801, 0] := by
  decide +kernel

end QECKChecks.A10K2
