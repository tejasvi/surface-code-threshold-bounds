import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5276 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5276 = true := by
  decide +kernel

theorem tot5276 : totK PA10K2 A10K2.t5276 = [0, 0, 532658819189, 1947440704500, 1848076508736, 447946825893, 26521581199, 0, 0, 0] := by
  decide +kernel

theorem rows5277 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5277 = true := by
  decide +kernel

theorem tot5277 : totK PA10K2 A10K2.t5277 = [0, 0, 0, 866271048262, 2395841781365, 1269080690129, 109920181304, 0, 0, 0] := by
  decide +kernel

theorem rows5278 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5278 = true := by
  decide +kernel

theorem tot5278 : totK PA10K2 A10K2.t5278 = [0, 554853825212, 1671110678928, 1515446883727, 549247190320, 338017869862, 109444031198, 6121173289, 0, 0] := by
  decide +kernel

theorem rows5279 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5279 = true := by
  decide +kernel

theorem tot5279 : totK PA10K2 A10K2.t5279 = [0, 195382624637, 1399405002446, 2234815018572, 928935079736, 74020752615, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
