import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12712 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12712 = true := by
  decide +kernel

theorem tot12712 : totK PD2M8K2 D2M8K2.t12712 = [0, 0, 208826168212, 488429642308, 211267936091, 10550414018, 0, 0] := by
  decide +kernel

theorem rows12713 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12713 = true := by
  decide +kernel

theorem tot12713 : totK PD2M8K2 D2M8K2.t12713 = [0, 0, 189594545487, 460980483984, 237961912815, 16700421822, 0, 0] := by
  decide +kernel

theorem rows12714 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12714 = true := by
  decide +kernel

theorem tot12714 : totK PD2M8K2 D2M8K2.t12714 = [0, 75480366365, 218219827807, 384973405474, 227017204533, 17949411884, 0, 0] := by
  decide +kernel

theorem rows12715 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12715 = true := by
  decide +kernel

theorem tot12715 : totK PD2M8K2 D2M8K2.t12715 = [0, 167441642278, 446316025677, 285799838677, 30097104265, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
