import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6796 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6796 = true := by
  decide +kernel

theorem tot6796 : totK PD2M8K2 D2M8K2.t6796 = [0, 0, 222661869551, 503391500936, 153021720936, 2484078857, 0, 0] := by
  decide +kernel

theorem rows6797 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6797 = true := by
  decide +kernel

theorem tot6797 : totK PD2M8K2 D2M8K2.t6797 = [178250561612, 388425051226, 135855143938, 95632644421, 88435646459, 6818291842, 0, 0] := by
  decide +kernel

theorem rows6798 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6798 = true := by
  decide +kernel

theorem tot6798 : totK PD2M8K2 D2M8K2.t6798 = [160546863760, 434251701557, 249776361897, 19671765876, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6799 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6799 = true := by
  decide +kernel

theorem tot6799 : totK PD2M8K2 D2M8K2.t6799 = [69195761676, 332539391904, 402645685525, 91487719936, 1369150432, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
