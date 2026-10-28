import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1616 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1616 = true := by
  decide +kernel

theorem tot1616 : totK PD2M8K2 D2M8K2.t1616 = [0, 0, 241163695007, 502778725064, 136051032416, 2309606161, 0, 0] := by
  decide +kernel

theorem rows1617 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1617 = true := by
  decide +kernel

theorem tot1617 : totK PD2M8K2 D2M8K2.t1617 = [0, 77354544009, 265018530038, 377563516697, 144709771202, 10740121073, 0, 0] := by
  decide +kernel

theorem rows1618 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1618 = true := by
  decide +kernel

theorem tot1618 : totK PD2M8K2 D2M8K2.t1618 = [0, 173922428963, 460144898087, 239965533843, 21197856955, 0, 0, 0] := by
  decide +kernel

theorem rows1619 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1619 = true := by
  decide +kernel

theorem tot1619 : totK PD2M8K2 D2M8K2.t1619 = [0, 156274309836, 459974424147, 263242343189, 16442401804, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
