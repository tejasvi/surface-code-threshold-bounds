import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14076 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14076 = true := by
  decide +kernel

theorem tot14076 : totK PD2M8K2 D2M8K2.t14076 = [0, 0, 173378232522, 448536023252, 250658826007, 19980618037, 0, 0] := by
  decide +kernel

theorem rows14077 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14077 = true := by
  decide +kernel

theorem tot14077 : totK PD2M8K2 D2M8K2.t14077 = [0, 0, 161633334422, 471891467876, 252778818560, 11564482653, 0, 0] := by
  decide +kernel

theorem rows14078 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14078 = true := by
  decide +kernel

theorem tot14078 : totK PD2M8K2 D2M8K2.t14078 = [0, 0, 210664419812, 469942754894, 209730066278, 14327823519, 0, 0] := by
  decide +kernel

theorem rows14079 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14079 = true := by
  decide +kernel

theorem tot14079 : totK PD2M8K2 D2M8K2.t14079 = [0, 0, 191055870542, 464602667493, 218641743462, 12370590376, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
