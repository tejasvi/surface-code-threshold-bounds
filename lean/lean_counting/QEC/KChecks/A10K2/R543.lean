import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2172 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2172 = true := by
  decide +kernel

theorem tot2172 : totK PA10K2 A10K2.t2172 = [0, 0, 27363690904, 1142681702759, 2267850903704, 987421722186, 97743242395, 0, 0, 0] := by
  decide +kernel

theorem rows2173 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2173 = true := by
  decide +kernel

theorem tot2173 : totK PA10K2 A10K2.t2173 = [404349054931, 1306467708132, 1267071542457, 467308261388, 591112715924, 623899233050, 167871307784, 6354482628, 0, 0] := by
  decide +kernel

theorem rows2174 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2174 = true := by
  decide +kernel

theorem tot2174 : totK PA10K2 A10K2.t2174 = [187751531253, 1163149395744, 2131328127348, 1288545326143, 260202556934, 20070762815, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2175 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2175 = true := by
  decide +kernel

theorem tot2175 : totK PA10K2 A10K2.t2175 = [361663300631, 1383256903829, 1983644464894, 1103975025522, 192610108749, 5300418178, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
