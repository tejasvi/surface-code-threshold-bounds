import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5956 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5956 = true := by
  decide +kernel

theorem tot5956 : totK PD2M8K2 D2M8K2.t5956 = [0, 89648142264, 324919165818, 365560595954, 132246428378, 15864095392, 0, 0] := by
  decide +kernel

theorem rows5957 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5957 = true := by
  decide +kernel

theorem tot5957 : totK PD2M8K2 D2M8K2.t5957 = [0, 0, 176509266180, 465070676793, 240580173214, 13530797253, 0, 0] := by
  decide +kernel

theorem rows5958 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5958 = true := by
  decide +kernel

theorem tot5958 : totK PD2M8K2 D2M8K2.t5958 = [0, 33042168431, 216175395034, 447514089050, 200076418714, 8214505460, 0, 0] := by
  decide +kernel

theorem rows5959 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5959 = true := by
  decide +kernel

theorem tot5959 : totK PD2M8K2 D2M8K2.t5959 = [0, 198482075558, 474233617491, 234828338946, 22055373437, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
