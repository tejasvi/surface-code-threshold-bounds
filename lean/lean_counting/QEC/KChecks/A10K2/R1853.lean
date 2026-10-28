import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7412 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7412 = true := by
  decide +kernel

theorem tot7412 : totK PA10K2 A10K2.t7412 = [0, 0, 0, 646173615998, 2062143086207, 1694042893207, 387259814580, 18429085292, 0, 0] := by
  decide +kernel

theorem rows7413 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7413 = true := by
  decide +kernel

theorem tot7413 : totK PA10K2 A10K2.t7413 = [0, 0, 324317460390, 1369920562093, 2106713826471, 1101533322814, 127504740051, 0, 0, 0] := by
  decide +kernel

theorem rows7414 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7414 = true := by
  decide +kernel

theorem tot7414 : totK PA10K2 A10K2.t7414 = [0, 0, 361564805494, 1668431090259, 2186495406367, 857143083090, 70445083173, 0, 0, 0] := by
  decide +kernel

theorem rows7415 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7415 = true := by
  decide +kernel

theorem tot7415 : totK PA10K2 A10K2.t7415 = [0, 0, 167781364357, 913077412801, 1929643567066, 1659027010741, 343957281282, 12692412833, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
