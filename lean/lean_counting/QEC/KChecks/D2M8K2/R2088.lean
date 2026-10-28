import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8352 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8352 = true := by
  decide +kernel

theorem tot8352 : totK PD2M8K2 D2M8K2.t8352 = [178965715709, 454739952085, 267636490422, 27776903183, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8353 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8353 = true := by
  decide +kernel

theorem tot8353 : totK PD2M8K2 D2M8K2.t8353 = [129939324550, 443535278114, 310250992962, 36507218619, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8354 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8354 = true := by
  decide +kernel

theorem tot8354 : totK PD2M8K2 D2M8K2.t8354 = [0, 191027174150, 460332058999, 238036332030, 24054838406, 0, 0, 0] := by
  decide +kernel

theorem rows8355 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8355 = true := by
  decide +kernel

theorem tot8355 : totK PD2M8K2 D2M8K2.t8355 = [84333515894, 248780678729, 363537636826, 189185295967, 10809146906, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
