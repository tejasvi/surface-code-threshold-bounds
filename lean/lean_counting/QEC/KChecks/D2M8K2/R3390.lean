import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13560 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13560 = true := by
  decide +kernel

theorem tot13560 : totK PD2M8K2 D2M8K2.t13560 = [0, 153034649092, 475404869720, 264765263568, 15017903740, 0, 0, 0] := by
  decide +kernel

theorem rows13561 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13561 = true := by
  decide +kernel

theorem tot13561 : totK PD2M8K2 D2M8K2.t13561 = [0, 187971764547, 452996228337, 239566700724, 22677803857, 0, 0, 0] := by
  decide +kernel

theorem rows13562 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13562 = true := by
  decide +kernel

theorem tot13562 : totK PD2M8K2 D2M8K2.t13562 = [0, 195354435919, 470740006476, 211924001976, 12183533023, 0, 0, 0] := by
  decide +kernel

theorem rows13563 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13563 = true := by
  decide +kernel

theorem tot13563 : totK PD2M8K2 D2M8K2.t13563 = [0, 52183488939, 336855343862, 407697692323, 81059219476, 1162935789, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
