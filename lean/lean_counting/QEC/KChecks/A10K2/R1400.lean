import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5600 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5600 = true := by
  decide +kernel

theorem tot5600 : totK PA10K2 A10K2.t5600 = [0, 0, 593115420863, 1971508172347, 1912800548175, 529248665674, 30423939859, 0, 0, 0] := by
  decide +kernel

theorem rows5601 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5601 = true := by
  decide +kernel

theorem tot5601 : totK PA10K2 A10K2.t5601 = [0, 0, 0, 771559771474, 2288558700215, 1688454668759, 240823955623, 6066958478, 0, 0] := by
  decide +kernel

theorem rows5602 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5602 = true := by
  decide +kernel

theorem tot5602 : totK PA10K2 A10K2.t5602 = [0, 0, 580293892768, 1927083669895, 1788167365011, 495623882280, 52179476137, 0, 0, 0] := by
  decide +kernel

theorem rows5603 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5603 = true := by
  decide +kernel

theorem tot5603 : totK PA10K2 A10K2.t5603 = [0, 0, 262705834922, 1393389402550, 2126561759139, 877920946801, 63106821706, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
