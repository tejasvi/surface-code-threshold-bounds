import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows116 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t116 = true := by
  decide +kernel

theorem tot116 : totK PA10K2 A10K2.t116 = [0, 315590801309, 1216975805413, 1829527718550, 1106141899558, 227545341017, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows117 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t117 = true := by
  decide +kernel

theorem tot117 : totK PA10K2 A10K2.t117 = [0, 525957062547, 1930816013252, 1943559161875, 428588957927, 11765040145, 0, 0, 0, 0] := by
  decide +kernel

theorem rows118 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t118 = true := by
  decide +kernel

theorem tot118 : totK PA10K2 A10K2.t118 = [0, 0, 624424211811, 2037953743643, 1692283354365, 388247561872, 25371180993, 0, 0, 0] := by
  decide +kernel

theorem rows119 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t119 = true := by
  decide +kernel

theorem tot119 : totK PA10K2 A10K2.t119 = [0, 288483183456, 1232998604750, 1905296111259, 1156939238485, 179729042815, 5447185874, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
