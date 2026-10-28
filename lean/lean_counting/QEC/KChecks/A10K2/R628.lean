import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2512 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2512 = true := by
  decide +kernel

theorem tot2512 : totK PA10K2 A10K2.t2512 = [0, 302082434609, 1491057755771, 2058432944928, 704448768517, 52519180279, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2513 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2513 = true := by
  decide +kernel

theorem tot2513 : totK PA10K2 A10K2.t2513 = [311517321411, 749008909333, 842822268005, 1499266221806, 1090646239087, 219157925173, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows2514 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2514 = true := by
  decide +kernel

theorem tot2514 : totK PA10K2 A10K2.t2514 = [499730976493, 1889382412091, 2038576496409, 572206151185, 32780555804, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2515 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2515 = true := by
  decide +kernel

theorem tot2515 : totK PA10K2 A10K2.t2515 = [0, 756265472100, 2164045117224, 1691554114576, 397870311772, 25715051306, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
