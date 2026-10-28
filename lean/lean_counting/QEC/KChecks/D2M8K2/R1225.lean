import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4900 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4900 = true := by
  decide +kernel

theorem tot4900 : totK PD2M8K2 D2M8K2.t4900 = [0, 0, 108879669206, 410514466966, 327777508711, 41352351096, 0, 0] := by
  decide +kernel

theorem rows4901 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4901 = true := by
  decide +kernel

theorem tot4901 : totK PD2M8K2 D2M8K2.t4901 = [0, 0, 0, 221690215708, 483999443701, 175936569978, 8470662040, 0] := by
  decide +kernel

theorem rows4902 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4902 = true := by
  decide +kernel

theorem tot4902 : totK PD2M8K2 D2M8K2.t4902 = [0, 0, 98389849845, 333679550158, 340195756379, 93671213301, 3581949829, 0] := by
  decide +kernel

theorem rows4903 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4903 = true := by
  decide +kernel

theorem tot4903 : totK PD2M8K2 D2M8K2.t4903 = [0, 0, 165277744889, 434812122280, 272691640459, 29719848591, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
