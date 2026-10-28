import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4084 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4084 = true := by
  decide +kernel

theorem tot4084 : totK PD2M8K2 D2M8K2.t4084 = [0, 0, 77611112426, 367801459911, 383466165649, 63622326734, 0, 0] := by
  decide +kernel

theorem rows4085 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4085 = true := by
  decide +kernel

theorem tot4085 : totK PD2M8K2 D2M8K2.t4085 = [0, 0, 0, 195492074640, 461742779389, 182638630586, 9072174562, 0] := by
  decide +kernel

theorem rows4086 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4086 = true := by
  decide +kernel

theorem tot4086 : totK PD2M8K2 D2M8K2.t4086 = [0, 0, 163157230524, 450436565556, 261423439466, 23448868100, 0, 0] := by
  decide +kernel

theorem rows4087 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4087 = true := by
  decide +kernel

theorem tot4087 : totK PD2M8K2 D2M8K2.t4087 = [0, 0, 172910568877, 471899683530, 240413862516, 12191915262, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
