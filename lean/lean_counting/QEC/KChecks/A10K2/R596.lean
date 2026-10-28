import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2384 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2384 = true := by
  decide +kernel

theorem tot2384 : totK PA10K2 A10K2.t2384 = [0, 0, 0, 932156403643, 2360803428926, 1157153463296, 105798247741, 0, 0, 0] := by
  decide +kernel

theorem rows2385 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2385 = true := by
  decide +kernel

theorem tot2385 : totK PA10K2 A10K2.t2385 = [0, 0, 0, 583429653365, 1955886124383, 1657269434394, 349569459132, 11740475125, 0, 0] := by
  decide +kernel

theorem rows2386 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2386 = true := by
  decide +kernel

theorem tot2386 : totK PA10K2 A10K2.t2386 = [0, 0, 0, 469081322973, 1860805047664, 1823808434806, 453734488750, 31690778550, 0, 0] := by
  decide +kernel

theorem rows2387 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2387 = true := by
  decide +kernel

theorem tot2387 : totK PA10K2 A10K2.t2387 = [0, 0, 0, 632994004223, 2069582860852, 1641382353723, 261077917946, 6354609102, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
