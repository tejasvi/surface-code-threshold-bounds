import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12176 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12176 = true := by
  decide +kernel

theorem tot12176 : totK PD2M8K2 D2M8K2.t12176 = [87179432255, 329981551247, 367144303434, 97459404500, 3462014130, 0, 0, 0] := by
  decide +kernel

theorem rows12177 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12177 = true := by
  decide +kernel

theorem tot12177 : totK PD2M8K2 D2M8K2.t12177 = [164151363175, 449918395163, 269709163008, 25995498543, 0, 0, 0, 0] := by
  decide +kernel

theorem rows12178 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12178 = true := by
  decide +kernel

theorem tot12178 : totK PD2M8K2 D2M8K2.t12178 = [156124401511, 448877391973, 262148289916, 18712444055, 0, 0, 0, 0] := by
  decide +kernel

theorem rows12179 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12179 = true := by
  decide +kernel

theorem tot12179 : totK PD2M8K2 D2M8K2.t12179 = [0, 212632032312, 494080034190, 175965992549, 7233348802, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
