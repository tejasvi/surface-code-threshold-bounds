import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7308 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7308 = true := by
  decide +kernel

theorem tot7308 : totK PD2M8K2 D2M8K2.t7308 = [0, 158142883121, 374482287583, 273429039615, 108037035879, 6804944647, 0, 0] := by
  decide +kernel

theorem rows7309 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7309 = true := by
  decide +kernel

theorem tot7309 : totK PD2M8K2 D2M8K2.t7309 = [0, 177805552528, 442820777828, 266000706727, 25176653962, 0, 0, 0] := by
  decide +kernel

theorem rows7310 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7310 = true := by
  decide +kernel

theorem tot7310 : totK PD2M8K2 D2M8K2.t7310 = [0, 87489962043, 370293324765, 369828300522, 58044203287, 0, 0, 0] := by
  decide +kernel

theorem rows7311 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7311 = true := by
  decide +kernel

theorem tot7311 : totK PD2M8K2 D2M8K2.t7311 = [0, 0, 266400063150, 487538835883, 148443968233, 8402921910, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
