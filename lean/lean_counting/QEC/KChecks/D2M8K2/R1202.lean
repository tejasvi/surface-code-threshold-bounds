import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4808 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4808 = true := by
  decide +kernel

theorem tot4808 : totK PD2M8K2 D2M8K2.t4808 = [0, 0, 88334427085, 346240770414, 365433239215, 69042444526, 1310285577, 0] := by
  decide +kernel

theorem rows4809 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4809 = true := by
  decide +kernel

theorem tot4809 : totK PD2M8K2 D2M8K2.t4809 = [0, 0, 52685718448, 356012101948, 448489513120, 46585331289, 0, 0] := by
  decide +kernel

theorem rows4810 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4810 = true := by
  decide +kernel

theorem tot4810 : totK PD2M8K2 D2M8K2.t4810 = [0, 0, 169160913068, 453025810948, 273996548075, 27149995799, 0, 0] := by
  decide +kernel

theorem rows4811 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4811 = true := by
  decide +kernel

theorem tot4811 : totK PD2M8K2 D2M8K2.t4811 = [0, 0, 194182208709, 489759117016, 229386844181, 9348026610, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
