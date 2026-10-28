import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7224 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7224 = true := by
  decide +kernel

theorem tot7224 : totK PD2M8K2 D2M8K2.t7224 = [0, 0, 40509881800, 344485661820, 423107818130, 66895262367, 1096505104, 0] := by
  decide +kernel

theorem rows7225 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7225 = true := by
  decide +kernel

theorem tot7225 : totK PD2M8K2 D2M8K2.t7225 = [0, 0, 47554338318, 283031456194, 434957246153, 98835614773, 3838026431, 0] := by
  decide +kernel

theorem rows7226 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7226 = true := by
  decide +kernel

theorem tot7226 : totK PD2M8K2 D2M8K2.t7226 = [0, 0, 192146564710, 483799636514, 220446068296, 6937287187, 0, 0] := by
  decide +kernel

theorem rows7227 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7227 = true := by
  decide +kernel

theorem tot7227 : totK PD2M8K2 D2M8K2.t7227 = [0, 0, 173539495509, 453676298085, 247319745053, 16424169734, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
