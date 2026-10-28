import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6644 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6644 = true := by
  decide +kernel

theorem tot6644 : totK PA10K2 A10K2.t6644 = [17057514467, 780543955421, 2117192766059, 1599596227211, 367118653844, 25371180993, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6645 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6645 = true := by
  decide +kernel

theorem tot6645 : totK PA10K2 A10K2.t6645 = [207188778170, 1015580829116, 1851206554634, 1343283387079, 237610532953, 5460492893, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6646 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6646 = true := by
  decide +kernel

theorem tot6646 : totK PA10K2 A10K2.t6646 = [375292226984, 1669244003237, 2015412614718, 609995330840, 37970647033, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6647 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6647 = true := by
  decide +kernel

theorem tot6647 : totK PA10K2 A10K2.t6647 = [185800768984, 985093637555, 1929979335578, 1293877035204, 218048600616, 6354482628, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
