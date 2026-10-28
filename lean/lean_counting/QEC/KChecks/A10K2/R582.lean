import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2328 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2328 = true := by
  decide +kernel

theorem tot2328 : totK PA10K2 A10K2.t2328 = [0, 0, 0, 824060301381, 2256580336294, 1676901353668, 315429196951, 6962742351, 0, 0] := by
  decide +kernel

theorem rows2329 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2329 = true := by
  decide +kernel

theorem tot2329 : totK PA10K2 A10K2.t2329 = [0, 396587084194, 1314051885422, 1312131847448, 729042582135, 796847210751, 358318725197, 34627912963, 0, 0] := by
  decide +kernel

theorem rows2330 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2330 = true := by
  decide +kernel

theorem tot2330 : totK PA10K2 A10K2.t2330 = [0, 164394757944, 1028036610058, 1865430941453, 1286249682471, 340553670933, 25371180993, 0, 0, 0] := by
  decide +kernel

theorem rows2331 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2331 = true := by
  decide +kernel

theorem tot2331 : totK PA10K2 A10K2.t2331 = [0, 257418524296, 1104105934683, 1906781374259, 1176507480014, 187760789094, 5460492893, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
