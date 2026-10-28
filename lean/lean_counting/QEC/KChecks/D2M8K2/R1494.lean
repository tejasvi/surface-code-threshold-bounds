import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5976 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5976 = true := by
  decide +kernel

theorem tot5976 : totK PD2M8K2 D2M8K2.t5976 = [0, 0, 193519610577, 464963321508, 234555136923, 12844960481, 0, 0] := by
  decide +kernel

theorem rows5977 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5977 = true := by
  decide +kernel

theorem tot5977 : totK PD2M8K2 D2M8K2.t5977 = [0, 0, 88555651143, 413634802467, 366811871962, 47305535320, 0, 0] := by
  decide +kernel

theorem rows5978 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5978 = true := by
  decide +kernel

theorem tot5978 : totK PD2M8K2 D2M8K2.t5978 = [0, 0, 0, 172652016508, 442258249919, 248375747458, 25191558099, 0] := by
  decide +kernel

theorem rows5979 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5979 = true := by
  decide +kernel

theorem tot5979 : totK PD2M8K2 D2M8K2.t5979 = [0, 0, 0, 172871062976, 475343748703, 219974814471, 7473384741, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
