import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3264 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3264 = true := by
  decide +kernel

theorem tot3264 : totK PA10K2 A10K2.t3264 = [0, 527310909255, 1919470945165, 1945857678874, 475436330988, 12244162943, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3265 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3265 = true := by
  decide +kernel

theorem tot3265 : totK PA10K2 A10K2.t3265 = [0, 0, 629887449944, 2026339883172, 1739439715198, 413479060805, 25734533292, 0, 0, 0] := by
  decide +kernel

theorem rows3266 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3266 = true := by
  decide +kernel

theorem tot3266 : totK PA10K2 A10K2.t3266 = [0, 176986670399, 994861256628, 1897924710146, 1340732352085, 233222409891, 6034215561, 0, 0, 0] := by
  decide +kernel

theorem rows3267 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3267 = true := by
  decide +kernel

theorem tot3267 : totK PA10K2 A10K2.t3267 = [0, 583381828075, 1904101209573, 1782102179477, 504655972143, 31941609474, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
