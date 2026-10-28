import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7940 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7940 = true := by
  decide +kernel

theorem tot7940 : totK PA10K2 A10K2.t7940 = [0, 0, 0, 759419077309, 2206103683034, 1653735641484, 276031220736, 7047025452, 0, 0] := by
  decide +kernel

theorem rows7941 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7941 = true := by
  decide +kernel

theorem tot7941 : totK PA10K2 A10K2.t7941 = [0, 0, 563781224979, 1864651830841, 1855207145520, 655550026700, 50403516269, 0, 0, 0] := by
  decide +kernel

theorem rows7942 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7942 = true := by
  decide +kernel

theorem tot7942 : totK PA10K2 A10K2.t7942 = [0, 0, 331364255318, 1580512748058, 2187754645136, 858582953110, 62972848401, 0, 0, 0] := by
  decide +kernel

theorem rows7943 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7943 = true := by
  decide +kernel

theorem tot7943 : totK PA10K2 A10K2.t7943 = [0, 0, 0, 568387718932, 2020973045035, 1926729797121, 395674612583, 12224107035, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
