import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7644 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7644 = true := by
  decide +kernel

theorem tot7644 : totK PA10K2 A10K2.t7644 = [0, 0, 0, 290905383052, 1382898252254, 2144946550185, 1051462276000, 106578524837, 0, 0] := by
  decide +kernel

theorem rows7645 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7645 = true := by
  decide +kernel

theorem tot7645 : totK PA10K2 A10K2.t7645 = [0, 0, 0, 30569183336, 561931634112, 1794725911162, 1729797665036, 471334360776, 31082886609, 0] := by
  decide +kernel

theorem rows7646 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7646 = true := by
  decide +kernel

theorem tot7646 : totK PA10K2 A10K2.t7646 = [0, 0, 0, 544361925266, 1840120161459, 1743224683618, 480514144362, 31936107789, 0, 0] := by
  decide +kernel

theorem rows7647 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7647 = true := by
  decide +kernel

theorem tot7647 : totK PA10K2 A10K2.t7647 = [0, 0, 0, 108061833447, 1212910319988, 2227471867745, 902289325494, 71978678543, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
