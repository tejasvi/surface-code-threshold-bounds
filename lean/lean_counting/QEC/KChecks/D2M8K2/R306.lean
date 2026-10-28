import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1224 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1224 = true := by
  decide +kernel

theorem tot1224 : totK PD2M8K2 D2M8K2.t1224 = [173108872798, 453428525120, 258145796474, 18930247270, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1225 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1225 = true := by
  decide +kernel

theorem tot1225 : totK PD2M8K2 D2M8K2.t1225 = [92999530293, 353549997621, 374680369507, 77760748259, 1267860612, 0, 0, 0] := by
  decide +kernel

theorem rows1226 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1226 = true := by
  decide +kernel

theorem tot1226 : totK PD2M8K2 D2M8K2.t1226 = [0, 262214558126, 493348544827, 141249828952, 3693668399, 0, 0, 0] := by
  decide +kernel

theorem rows1227 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1227 = true := by
  decide +kernel

theorem tot1227 : totK PD2M8K2 D2M8K2.t1227 = [0, 186324877679, 466404471210, 226073187162, 17066492788, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
