import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6752 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6752 = true := by
  decide +kernel

theorem tot6752 : totK PD2M8K2 D2M8K2.t6752 = [0, 171911634066, 473098521938, 236804216344, 12696286041, 0, 0, 0] := by
  decide +kernel

theorem rows6753 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6753 = true := by
  decide +kernel

theorem tot6753 : totK PD2M8K2 D2M8K2.t6753 = [0, 208830512984, 462077658171, 203700846378, 12595094539, 0, 0, 0] := by
  decide +kernel

theorem rows6754 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6754 = true := by
  decide +kernel

theorem tot6754 : totK PD2M8K2 D2M8K2.t6754 = [0, 150732971402, 465268536691, 243031182305, 15689984814, 0, 0, 0] := by
  decide +kernel

theorem rows6755 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6755 = true := by
  decide +kernel

theorem tot6755 : totK PD2M8K2 D2M8K2.t6755 = [0, 192644727711, 484745407925, 209827207596, 7807117139, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
