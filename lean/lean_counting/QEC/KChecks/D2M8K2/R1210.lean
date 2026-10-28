import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4840 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4840 = true := by
  decide +kernel

theorem tot4840 : totK PD2M8K2 D2M8K2.t4840 = [0, 0, 207756474831, 503396648190, 195712731020, 9407265020, 0, 0] := by
  decide +kernel

theorem rows4841 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4841 = true := by
  decide +kernel

theorem tot4841 : totK PD2M8K2 D2M8K2.t4841 = [0, 0, 33847987942, 315226691253, 455026720155, 110451032701, 4143089693, 0] := by
  decide +kernel

theorem rows4842 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4842 = true := by
  decide +kernel

theorem tot4842 : totK PD2M8K2 D2M8K2.t4842 = [0, 0, 69759220461, 330069558320, 399044064057, 86227217444, 1227322468, 0] := by
  decide +kernel

theorem rows4843 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4843 = true := by
  decide +kernel

theorem tot4843 : totK PD2M8K2 D2M8K2.t4843 = [0, 0, 182899090761, 459742778607, 267396707934, 28064901325, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
