import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12116 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12116 = true := by
  decide +kernel

theorem tot12116 : totK PD2M8K2 D2M8K2.t12116 = [0, 0, 178718781984, 467964235545, 230328354328, 14920370633, 0, 0] := by
  decide +kernel

theorem rows12117 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12117 = true := by
  decide +kernel

theorem tot12117 : totK PD2M8K2 D2M8K2.t12117 = [0, 0, 0, 305315543830, 448026804829, 76027763179, 1032241984, 0] := by
  decide +kernel

theorem rows12118 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12118 = true := by
  decide +kernel

theorem tot12118 : totK PD2M8K2 D2M8K2.t12118 = [0, 0, 135510909567, 356058545665, 272230836510, 73355662429, 3598673838, 0] := by
  decide +kernel

theorem rows12119 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12119 = true := by
  decide +kernel

theorem tot12119 : totK PD2M8K2 D2M8K2.t12119 = [0, 0, 193930222299, 469608590508, 224962715018, 16097491677, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
