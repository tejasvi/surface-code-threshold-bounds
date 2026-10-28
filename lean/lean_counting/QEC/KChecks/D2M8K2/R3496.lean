import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13984 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13984 = true := by
  decide +kernel

theorem tot13984 : totK PD2M8K2 D2M8K2.t13984 = [0, 0, 34532533563, 379303823807, 434502067092, 53184874021, 0, 0] := by
  decide +kernel

theorem rows13985 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13985 = true := by
  decide +kernel

theorem tot13985 : totK PD2M8K2 D2M8K2.t13985 = [0, 0, 49447098536, 227523307442, 421611122321, 140325863516, 5126512042, 0] := by
  decide +kernel

theorem rows13986 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13986 = true := by
  decide +kernel

theorem tot13986 : totK PD2M8K2 D2M8K2.t13986 = [0, 0, 174042520847, 460011578311, 250520588802, 21922323184, 0, 0] := by
  decide +kernel

theorem rows13987 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13987 = true := by
  decide +kernel

theorem tot13987 : totK PD2M8K2 D2M8K2.t13987 = [0, 0, 174292431249, 455878458341, 234458949902, 13182661443, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
