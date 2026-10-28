import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5704 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5704 = true := by
  decide +kernel

theorem tot5704 : totK PA10K2 A10K2.t5704 = [0, 285008661260, 1220722893941, 1868688729567, 1106093970217, 189150301515, 5460492893, 0, 0, 0] := by
  decide +kernel

theorem rows5705 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5705 = true := by
  decide +kernel

theorem tot5705 : totK PA10K2 A10K2.t5705 = [0, 501369278675, 1839075530158, 1934296827705, 524362614076, 26519445934, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5706 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5706 = true := by
  decide +kernel

theorem tot5706 : totK PA10K2 A10K2.t5706 = [0, 0, 783388484978, 2303188647018, 1495068193047, 169330486188, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5707 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5707 = true := by
  decide +kernel

theorem tot5707 : totK PA10K2 A10K2.t5707 = [0, 458520426296, 1674062128336, 1843385411303, 738853494272, 138557600286, 6354482628, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
