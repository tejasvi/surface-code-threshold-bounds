import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8112 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8112 = true := by
  decide +kernel

theorem tot8112 : totK PA10K2 A10K2.t8112 = [0, 0, 526618122485, 1868395514561, 2019212020971, 596702354375, 40597686310, 0, 0, 0] := by
  decide +kernel

theorem rows8113 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8113 = true := by
  decide +kernel

theorem tot8113 : totK PA10K2 A10K2.t8113 = [0, 0, 192874205643, 1178682804432, 2137804197735, 1326363561614, 231686268721, 6853348008, 0, 0] := by
  decide +kernel

theorem rows8114 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8114 = true := by
  decide +kernel

theorem tot8114 : totK PA10K2 A10K2.t8114 = [0, 0, 0, 538854696659, 2035068975721, 2103754934709, 480275865257, 12853939499, 0, 0] := by
  decide +kernel

theorem rows8115 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8115 = true := by
  decide +kernel

theorem tot8115 : totK PA10K2 A10K2.t8115 = [0, 0, 0, 509919795312, 1665826362789, 1826083374410, 705773261609, 61909773057, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
