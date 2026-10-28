import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1976 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1976 = true := by
  decide +kernel

theorem tot1976 : totK PD2M8K2 D2M8K2.t1976 = [0, 0, 180381991424, 451375010771, 255186236543, 25373788367, 0, 0] := by
  decide +kernel

theorem rows1977 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1977 = true := by
  decide +kernel

theorem tot1977 : totK PD2M8K2 D2M8K2.t1977 = [0, 0, 191970962892, 500419319927, 200189490577, 5430665091, 0, 0] := by
  decide +kernel

theorem rows1978 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1978 = true := by
  decide +kernel

theorem tot1978 : totK PD2M8K2 D2M8K2.t1978 = [0, 161409309764, 397271863841, 257165024116, 90408809805, 6804944647, 0, 0] := by
  decide +kernel

theorem rows1979 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1979 = true := by
  decide +kernel

theorem tot1979 : totK PD2M8K2 D2M8K2.t1979 = [0, 177710039915, 472709097874, 237032261625, 14131733378, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
