import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2824 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2824 = true := by
  decide +kernel

theorem tot2824 : totK PD2M8K2 D2M8K2.t2824 = [0, 212204381749, 496826648930, 196443391207, 5430665091, 0, 0, 0] := by
  decide +kernel

theorem rows2825 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2825 = true := by
  decide +kernel

theorem tot2825 : totK PD2M8K2 D2M8K2.t2825 = [160996825849, 370276749132, 263274612438, 110246998359, 6804944647, 0, 0, 0] := by
  decide +kernel

theorem rows2826 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2826 = true := by
  decide +kernel

theorem tot2826 : totK PD2M8K2 D2M8K2.t2826 = [178215915361, 452919690645, 261122696422, 20025104483, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2827 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2827 = true := by
  decide +kernel

theorem tot2827 : totK PD2M8K2 D2M8K2.t2827 = [87486175482, 364837162743, 363644495645, 68216060676, 1163840124, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
